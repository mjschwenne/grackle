package main

import (
	"bytes"
	"flag"
	"fmt"
	"io/fs"
	"log"
	"os"
	"os/exec"
	"path"
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

type CoqOutput struct {
	ProjectName    string
	Name           string
	GooseOutput    string
	NestedMessages []string
	Fields         []*field
}

var protoFieldMap = map[int]string{
	50621: "coq_logical_path",
	50622: "coq_physical_path",
	50623: "goose_output_path",
}

const COQ_LOGICAL_PATH_FIELD_TAG = 50621
const COQ_PHYSICAL_PATH_FIELD_TAG = 50622
const GOOSE_OUTPUT_PATH = 50623

var typeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "u32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "u32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "u32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "u64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "u64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "u64",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "message",
}

var refTypeMap = map[fieldType]bool{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   false,
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  false,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: false,
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   false,
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  false,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: false,
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: true,
}

func getCoqOutputPath(coqPhysicalPath string, messageName string) string {
	return path.Join(coqPhysicalPath, messageName+"_proof.v")
}

func getCoqTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName()
	}
	return typeMap[field.GetType()]
}

func filter[T any](slice []T, f func(T) bool) []T {
	var n []T
	for _, e := range slice {
		if f(e) {
			n = append(n, e)
		}
	}
	return n
}

func getRefFields(fields []*field) []*field {
	return filter(fields, isReferenceType)
}

func isReferenceType(field *field) bool {
	return refTypeMap[field.GetType()]
}

func join(sep string, s ...string) string {
	return strings.Join(s, sep)
}

func main() {
	// Parse command line arguments
	var gooseOutputPath = flag.String("goose-output", "", "Directory to write the goose output")
	var coqLogicalPath = flag.String("coq-logical-path", "", "Logical path to import the marshal proofs from")
	var coqPhysicalPath = flag.String("coq-physical-path", "", "Physical output path for coq proofs")
	var debug = flag.Bool("debug", false, "Output all generated code to stdout")
	// var goOutputPath = flag.String("go-output-path", "", "Physical path to output go code into")
	// var goPackageName = flag.String("go-package-name", "", "Name for the autogrenerated go package")
	flag.Parse()

	var protoFiles = flag.Args()
	if len(protoFiles) < 1 {
		fmt.Println("Usage: grackle [options] proto-files ...")
		os.Exit(1)
	}

	// Generate proto descriptor in temp file
	descirptorFile, err := os.CreateTemp("", "grackle-")
	if err != nil {
		log.Fatalf("Failed to create temporary descriptor file: %v", err)
	}
	descirptorName := descirptorFile.Name()

	// Remove descriptor file at the end of the program
	defer descirptorFile.Close()
	defer os.Remove(descirptorName)

	protoc := exec.Command("protoc", append([]string{"--descriptor_set_out=" + descirptorName, "--proto_path=src/proto/", "--proto_path=."}, protoFiles...)...)
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

	// Load templates
	var tmplFiles []string
	err = filepath.WalkDir("src/templates/",
		func(path string, info fs.DirEntry, err error) error {
			if !info.IsDir() {
				tmplFiles = append(tmplFiles, path)
			}
			return nil
		})

	tmpl := template.New("coq").Delims("<<", ">>")
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
		"pred": func(i int) int { return i - 1 },
		"succ": func(i int) int { return i + 1 },
	}
	tmpl, err = tmpl.Funcs(funcMap).ParseFiles(tmplFiles...)
	if err != nil {
		panic(err)
	}

	for _, file := range fileDescriptorSet.File {
		fileCoqLogicalPath := *coqLogicalPath
		fileCoqPhysicalPath := *coqPhysicalPath
		// Get grackle options
		if file.GetOptions() != nil {
			fmt.Printf("File Options: ``%v``\n", file.GetOptions().String())
			regex := regexp.MustCompile(`(?<field>\d+):"(?<value>[^"]+)"`)
			for _, match := range regex.FindAllStringSubmatch(file.GetOptions().String(), -1) {
				field, _ := strconv.Atoi(match[1])
				switch field {
				case COQ_LOGICAL_PATH_FIELD_TAG:
					fileCoqLogicalPath = match[2]
					fmt.Printf("coq logical path: %v\n", match[2])
				case COQ_PHYSICAL_PATH_FIELD_TAG:
					fileCoqPhysicalPath = match[2]
					fmt.Printf("coq physical path: %v\n", match[2])
				}
			}
		}
		for _, message := range file.MessageType {
			coqFileName := getCoqOutputPath(fileCoqPhysicalPath, message.GetName())
			var coqFile *os.File
			if *debug {
				fmt.Printf("--- Begin: %s ---\n", coqFileName)
				coqFile = os.Stdout
			} else {
				coqFile, err = os.OpenFile(coqFileName, os.O_WRONLY|os.O_CREATE, 0644)
				if err != nil {
					log.Fatalf("Could not open output file: %v", err)
				}
			}
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

			co := CoqOutput{
				ProjectName:    fileCoqLogicalPath,
				Name:           *message.Name,
				GooseOutput:    *gooseOutputPath,
				NestedMessages: nested,
				Fields:         fields,
			}

			err = tmpl.ExecuteTemplate(coqFile, "coq_proof", co)
			if err != nil {
				panic(err)
			}

			if *debug {
				fmt.Printf("--- End: %s ---\n", coqFileName)
			}
		}
	}
}
