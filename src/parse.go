package main

import (
	"bytes"
	"io/fs"
	"log"
	"os"
	"path/filepath"
	"slices"
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
	descriptorFile := "src/timestamp_type.bin"
	descriptorContent, err := os.ReadFile(descriptorFile)
	if err != nil {
		log.Fatalf("Failed to read descriptor file: %v", err)
	}

	// Check if the file is not empty
	if len(descriptorContent) == 0 {
		log.Fatalf("Descriptor file is empty")
	}

	// Unmarshal the descriptor into a FileDescriptorSet
	var fileDescriptorSet descriptorpb.FileDescriptorSet
	if err := proto.Unmarshal(descriptorContent, &fileDescriptorSet); err != nil {
		log.Fatalf("Failed to unmarshal descriptor file: %v", err)
	}

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

	ts := fileDescriptorSet.File[0].MessageType[1]
	var fields []*field
	var nested []string
	for _, f := range ts.GetField() {
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
		ProjectName:    "Grackle.example",
		Name:           *ts.Name,
		GooseOutput:    "example",
		NestedMessages: nested,
		Fields:         fields,
	}

	err = tmpl.ExecuteTemplate(os.Stdout, "coq_proof", co)
	if err != nil {
		panic(err)
	}
}
