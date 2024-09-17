package main

import (
	"fmt"
	"io/fs"
	"log"
	"os"
	"path/filepath"
	"strings"
	"text/template"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

type field = descriptorpb.FieldDescriptorProto
type fieldType = descriptorpb.FieldDescriptorProto_Type

type CoqOutput struct {
	ProjectName string
	Name        string
	GooseOutput string
	ModuleName  string
	Fields      []*field
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

func getCoqTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName()
	}
	return typeMap[field.GetType()]
}

func getEncoding(field *field) string {
	coqType, ok := typeMap[field.GetType()]
	if !ok {
		panic("Attempted to get encoding of unsupported type")
	}

	var result string
	switch coqType {
	case "u32":
		result = fmt.Sprintf("(u32_le args.(%s))", field.GetName())
	case "u64":
		result = fmt.Sprintf("(u64_le args.(%s))", field.GetName())
	case "message":
		result = fmt.Sprintf("MESSAGES NOT SUPPORTED YET\n")
	}

	return result
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

func generateHasEncodingExistsQuant(fields []*field) string {
	nestedMessages := filter(fields, func(f *field) bool {
		return f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE
	})

	if len(nestedMessages) == 0 {
		return ""
	}

	resultBuilder := strings.Builder{}
	resultBuilder.WriteString("∃ (")
	for _, nestedMessage := range nestedMessages {
		resultBuilder.WriteString(fmt.Sprintf("%s_l", nestedMessage.GetName()))
	}
	resultBuilder.WriteString(": loc),\n")
	return resultBuilder.String()
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
	err = filepath.WalkDir("src/templates/", func(path string, info fs.DirEntry, err error) error {
		if !info.IsDir() {
			tmplFiles = append(tmplFiles, path)
		}
		return nil
	})

	funcMap := template.FuncMap{
		"coqType":  getCoqTypeName,
		"encoding": getEncoding,
		"exists":   generateHasEncodingExistsQuant,
	}
	tmpl, err := template.New("coq_record").Funcs(funcMap).Delims("<<", ">>").ParseFiles(tmplFiles...)
	if err != nil {
		panic(err)
	}

	ts := fileDescriptorSet.File[0].MessageType[0]
	var fields []*field
	for _, f := range ts.GetField() {
		fields = append(fields, f)
	}

	co := CoqOutput{
		ProjectName: "Grackel.example",
		Name:        *ts.Name,
		GooseOutput: "example",
		ModuleName:  *ts.Name,
		Fields:      fields,
	}

	err = tmpl.ExecuteTemplate(os.Stdout, "coq.tmpl", co)
	if err != nil {
		panic(err)
	}
}
