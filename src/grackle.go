package grackle

import (
	"bytes"
	"fmt"
	"go/format"
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

	"github.com/goose-lang/goose"
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

func generateDescirptor(protoDir *string) *descriptorpb.FileDescriptorSet {
	absProtoDir, err := filepath.Abs(*protoDir)
	if err != nil {
		log.Fatalf("Could not locate directory '%s': %v\n", *protoDir, err)
	}

	// Find the proto files in the protoDir
	var protoFiles []string
	filepath.WalkDir(*protoDir, func(path string, d fs.DirEntry, err error) error {
		relativePath, err := filepath.Rel(*protoDir, path)
		if err != nil {
			return err
		}

		if !d.Type().IsDir() && filepath.Ext(path) == ".proto" {
			protoFiles = append(protoFiles, relativePath)
		}

		return nil
	})
	// Generate proto descriptor in temp file
	descirptorFile, err := os.CreateTemp("", "grackle-")
	if err != nil {
		log.Fatalf("Failed to create temporary descriptor file: %v", err)
	}
	descirptorName := descirptorFile.Name()

	// Remove descriptor file at the end of the program
	defer descirptorFile.Close()
	defer os.Remove(descirptorName)

	protoc := exec.Command("protoc", append([]string{"--descriptor_set_out=" + descirptorName, "--proto_path=."}, protoFiles...)...)
	var protocErr bytes.Buffer
	protoc.Stderr = &protocErr
	protoc.Dir = absProtoDir
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
		"coqType":      getCoqTypeName,
		"isRef":        isReferenceType,
		"refFields":    getRefFields,
		"join":         join,
		"lower":        strings.ToLower,
		"pred":         func(i int) int { return i - 1 },
		"succ":         func(i int) int { return i + 1 },
		"goType":       getGoTypeName,
		"param":        generateParameterName,
		"marshalType":  getBuiltInMarshalFuncType,
		"cleanCoqName": cleanCoqName,
		"goName":       capitialize,
		// This is a bit of a hack to let me call templates with dynamic names
		"callTemplate": func(name string, data interface{}) (ret string, err error) {
			buf := bytes.NewBuffer([]byte{})
			err = tmpl.ExecuteTemplate(buf, name, data)
			ret = buf.String()
			return
		},
	}
	tmpl, err = tmpl.Funcs(funcMap).ParseFiles(tmplFiles...)
	if err != nil {
		panic(err)
	}

	return tmpl
}

// Override options with file-specific values if needed
func getFileOptions(file *descriptorpb.FileDescriptorProto, gooseOutput *string, coqLogicalPath *string, coqPhysicalPath *string, goModule *string, goRoot *string, goOutputPath *string, goPackage *string) *fileParams {
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

	return &fileParams{
		GooseOutput:     fileGooseOutput,
		CoqLogicalPath:  fileCoqLogicalPath,
		CoqPhysicalPath: fileCoqPhysicalPath,
		GoOutputPath:    goOutputPath,
		GoPackage:       goPackage,
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

func gooseTranslate(gooseOutput *string, goRoot string, goDirectory string) {
	gooseConfig := goose.TranslationConfig{TypeCheck: false, AddSourceFileComments: false, SkipInterfaces: false}
	goAbs, err := filepath.Abs(goDirectory)
	log.Printf("Translating '%s' from go root '%s'\n", goAbs, goRoot)
	gooseFiles, gooseErrs, err := gooseConfig.TranslatePackages(goRoot, goAbs)
	if err != nil {
		log.Fatalf("Could not generate goose code: %v\n", err)
	}

	for _, ge := range gooseErrs {
		if ge != nil {
			log.Printf("Warning: Goose error: %v\n", ge)
		}
	}

	for _, gf := range gooseFiles {
		gooseFilePath := filepath.Join(*gooseOutput, gf.GoPackage+".v")
		gooseFile := openGrackleFile(&gooseFilePath)
		fmt.Printf("--- GOOSE Begin: %s ---\n", gooseFilePath)
		gf.Write(os.Stdout)
		gf.Write(gooseFile)
		fmt.Printf("--- GOOSE End: %s ---\n", gooseFilePath)
	}
}

func Grackle(protoDir *string, gooseOutput *string, coqLogicalPath *string, coqPhysicalPath *string, goOutputPath *string, goPackage *string, debug io.Writer) {
	tmpl := setupTemplates()
	goModule, goRoot := findGoModuleName(*goOutputPath)
	createOutputDirectories(gooseOutput, coqPhysicalPath, goOutputPath)

	goFiles := make([]*string, 0, 10)
	for _, file := range generateDescirptor(protoDir).File {
		fileOpts := getFileOptions(file, gooseOutput, coqLogicalPath, coqPhysicalPath, &goModule, &goRoot, goOutputPath, goPackage)
		for _, message := range file.MessageType {
			msg := getMessageOptions(message, fileOpts)
			var coqOut io.Writer
			var goOut io.Writer
			if debug != nil {
				coqOut = debug
				goOut = debug
				fmt.Fprintf(debug, "--- Begin: %s ---\n", *msg.CoqPhysicalPath)
			} else {
				coqOut = openGrackleFile(msg.CoqPhysicalPath)
				goOut = openGrackleFile(msg.GoPhysicalPath)
				goFiles = append(goFiles, msg.GoPhysicalPath)
			}

			err := tmpl.ExecuteTemplate(coqOut, "coq_proof", msg)

			if err != nil {
				log.Fatalf("Error generating coq code: %v\n", err)
			}
			if debug != nil {
				fmt.Fprintf(debug, "--- End: %s ---\n", *msg.CoqPhysicalPath)
				fmt.Fprintf(debug, "--- Start: %s ---\n", *msg.GoPhysicalPath)
			}

			// Write to a buffer, then format
			// The buffer may seem large, but it is only 1 MB
			goBuffer := bytes.NewBuffer(make([]byte, 0, 1000000))
			err = tmpl.ExecuteTemplate(goBuffer, "go_file", msg)
			if err != nil {
				log.Fatalf("Error generating go code: %v\n", err)
			}

			formattedGo, err := format.Source(goBuffer.Bytes())
			if err != nil {
				log.Fatalf("Error formatting go code: %v\n", err)
			}

			_, err = goOut.Write(formattedGo)
			if err != nil {
				log.Fatalf("Error writing go code: %v\n", err)
			}

			if debug != nil {
				fmt.Fprintf(debug, "--- End: %s ---\n", *msg.GoPhysicalPath)
			}

			// Goose Translation, but only during actual grackle usage
			if debug == nil {
				gooseTranslate(gooseOutput, goRoot, filepath.Dir(*msg.GoPhysicalPath))
			}
		}
	}
}
