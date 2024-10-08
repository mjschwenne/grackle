package main

import (
	"bytes"
	"fmt"
	"io"
	"io/fs"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"text/template"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

type field = descriptorpb.FieldDescriptorProto
type fieldType = descriptorpb.FieldDescriptorProto_Type

type fileParams struct {
	GooseOutput     *string
	CoqLogicalPath  *string
	CoqPhysicalPath *string
	GoOutputPath    *string
	GoPackage       *string
}

type messageParams struct {
	Name            *string
	GooseOutput     *string
	CoqLogicalPath  *string
	CoqPhysicalPath *string
	GoPhysicalPath  *string
	GoPackage       *string
	NestedMessages  []string
	Fields          []*field
}

func generateDescirptor(protoFiles *[]string) *descriptorpb.FileDescriptorSet {
	// Generate proto descriptor in temp file
	descirptorFile, err := os.CreateTemp("", "grackle-")
	if err != nil {
		log.Fatalf("Failed to create temporary descriptor file: %v", err)
	}
	descirptorName := descirptorFile.Name()

	// Remove descriptor file at the end of the program
	defer descirptorFile.Close()
	defer os.Remove(descirptorName)

	grackleProtoDir := getModulePath("proto/")
	protoc := exec.Command("protoc", append([]string{"--descriptor_set_out=" + descirptorName, "--proto_path=" + grackleProtoDir, "--proto_path=."}, *protoFiles...)...)
	var protocErr bytes.Buffer
	protoc.Stderr = &protocErr
	err = protoc.Run()
	if err != nil {
		log.Print(protocErr.String())
		log.Fatalf("Error generating proto descriptor file: %v", err)
	}

	// Load descriptor
	var fileDescriptorSet descriptorpb.FileDescriptorSet
	protoContent, err := os.ReadFile(descirptorName)
	if err != nil {
		log.Fatalf("Failed to read descriptor file: %v", err)
	}

	if len(protoContent) == 0 {
		log.Fatalf("Descriptor file %s is empty.", descirptorName)
	}

	if err := (proto.UnmarshalOptions{DiscardUnknown: false}).Unmarshal(protoContent, &fileDescriptorSet); err != nil {
		log.Fatalf("Failed to unmarshal descriptor file: %v", err)
	}

	return &fileDescriptorSet
}

func setupTemplates() *template.Template {
	// Load templates
	var tmplFiles []string
	err := filepath.WalkDir(getModulePath("templates/"),
		func(path string, info fs.DirEntry, err error) error {
			if !info.IsDir() {
				tmplFiles = append(tmplFiles, path)
			}
			return nil
		})

	tmpl := template.New("grackle").Delims("<<", ">>")
	funcMap := template.FuncMap{
		"coqType":   getCoqTypeName,
		"isRef":     isReferenceType,
		"refFields": getRefFields,
		"join":      join,
		// This is a bit of a hack to let me call templates with dynamic names
		"callTemplate": func(name string, data interface{}) (ret string, err error) {
			buf := bytes.NewBuffer([]byte{})
			err = tmpl.ExecuteTemplate(buf, name, data)
			ret = buf.String()
			return
		},
		"pred":        func(i int) int { return i - 1 },
		"succ":        func(i int) int { return i + 1 },
		"goType":      getGoTypeName,
		"goName":      getGoPublicName,
		"param":       generateParameterName,
		"marshalType": getBuiltInMarshalFuncType,
	}
	tmpl, err = tmpl.Funcs(funcMap).ParseFiles(tmplFiles...)
	if err != nil {
		panic(err)
	}

	return tmpl
}

// Override options with file-specific values if needed
func getFileOptions(file *descriptorpb.FileDescriptorProto, gooseOutput *string, coqLogicalPath *string, coqPhysicalPath *string, goModule *string, goRoot *string, goOutputPath *string) *fileParams {
	const COQ_LOGICAL_PATH_FIELD_TAG = 50621
	const COQ_PHYSICAL_PATH_FIELD_TAG = 50622
	const GOOSE_OUTPUT_PATH = 50623

	var fileCoqLogicalPath = coqLogicalPath
	var fileCoqPhysicalPath = coqPhysicalPath
	var fileGooseOutput = gooseOutput

	if file.GetOptions() != nil {
		regex := regexp.MustCompile(`(?<field>\d+):"(?<value>[^"]+)"`)
		for _, match := range regex.FindAllStringSubmatch(file.GetOptions().String(), -1) {
			field, _ := strconv.Atoi(match[1])
			switch field {
			case COQ_LOGICAL_PATH_FIELD_TAG:
				fileCoqLogicalPath = &match[2]
			case COQ_PHYSICAL_PATH_FIELD_TAG:
				fileCoqPhysicalPath = &match[2]
			}
		}
	}

	goPackage := strings.TrimRight(strings.TrimPrefix(*goOutputPath, *goRoot), "/\\")
	return &fileParams{
		GooseOutput:     fileGooseOutput,
		CoqLogicalPath:  fileCoqLogicalPath,
		CoqPhysicalPath: fileCoqPhysicalPath,
		GoOutputPath:    goOutputPath,
		GoPackage:       &goPackage,
	}
}

func getMessageOptions(message *descriptorpb.DescriptorProto, fileOpts *fileParams) messageParams {
	var fields []*field
	var nested []string
	for _, f := range message.GetField() {
		if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
			realName := (f.GetTypeName())[1:]
			f.TypeName = &realName
			if !slices.Contains(nested, realName) {
				nested = append(nested, realName)
			}
		}
		fields = append(fields, f)
	}

	coqOutputPath := getCoqOutputPath(fileOpts.CoqPhysicalPath, message.Name)
	goOutputPath := getGoOutputPath(fileOpts.GoOutputPath, message.Name)
	messageOpts := messageParams{
		Name:            message.Name,
		GooseOutput:     fileOpts.GooseOutput,
		CoqLogicalPath:  fileOpts.CoqLogicalPath,
		CoqPhysicalPath: &coqOutputPath,
		GoPhysicalPath:  &goOutputPath,
		GoPackage:       fileOpts.GoPackage,
		NestedMessages:  nested,
		Fields:          fields,
	}

	return messageOpts
}

func openGrackleFile(path *string) *os.File {
	file, err := os.OpenFile(*path, os.O_WRONLY|os.O_CREATE, 0644)
	if err != nil {
		log.Fatalf("Could not open output file: %v\n", err)
	}

	return file
}

func grackle(protoFiles *[]string, gooseOutput *string, coqLogicalPath *string, coqPhysicalPath *string, goOutputPath *string, debug io.Writer) {
	tmpl := setupTemplates()
	goModule, goRoot := findGoModuleName(*goOutputPath)
	// absGoOutputPath, err := filepath.Abs(*goOutputPath)
	// if err != nil {
	// 	log.Fatalf("Cannot resolve go output path: %v\n", goOutputPath)
	// }

	for _, file := range generateDescirptor(protoFiles).File {
		fileOpts := getFileOptions(file, gooseOutput, coqLogicalPath, coqPhysicalPath, &goModule, &goRoot, goOutputPath)
		for _, message := range file.MessageType {
			msg := getMessageOptions(message, fileOpts)
			var coqOut io.Writer
			var goOut io.Writer
			if debug != nil {
				coqOut = debug
				goOut = debug
				fmt.Fprintf(coqOut, "--- Begin: %s ---\n", *msg.CoqPhysicalPath)
			} else {
				coqOut = openGrackleFile(msg.CoqPhysicalPath)
				goOut = openGrackleFile(msg.GoPhysicalPath)
			}

			err := tmpl.ExecuteTemplate(coqOut, "coq_proof", msg)

			if err != nil {
				log.Fatalf("Error generating coq code: %v\n", err)
			}
			if debug != nil {
				fmt.Fprintf(debug, "--- End: %s ---\n", *msg.CoqPhysicalPath)
				fmt.Fprintf(debug, "--- Start: %s ---\n", *msg.GoPhysicalPath)
			}

			err = tmpl.ExecuteTemplate(goOut, "go_file", msg)

			if err != nil {
				log.Fatalf("Error generating go code: %v\n", err)
			}
			if debug != nil {
				fmt.Fprintf(debug, "--- End: %s ---\n", *msg.GoPhysicalPath)
			}
		}
	}
}