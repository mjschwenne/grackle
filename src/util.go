package main

import (
	"bytes"
	"log"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"runtime"
	"strings"

	"golang.org/x/mod/modfile"
	"google.golang.org/protobuf/types/descriptorpb"
)

var coqTypeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "u32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "u32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "u32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "u64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "u64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "u64",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "message",
}

var goTypeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "uint64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "uint64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "uint64",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "message",
}

var marshalTypeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "Int32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "Int32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "Int32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "Int64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "Int64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "Int64",
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

// Searches up the file tree for the go.mod file.
// Returns both the name of the module listed in go.mod and the directory where
// the go.mod is found.
func findGoModuleName(goOutputPath string) (string, string) {

	goenv := exec.Command("go", "env", "GOMOD")
	var goenvOut, goenvErr bytes.Buffer
	goenv.Stderr = &goenvErr
	goenv.Stdout = &goenvOut
	err := goenv.Run()
	if err != nil {
		log.Print(goenvErr.String())
		log.Fatalf("Error finding go.mod path: %v\n", err)
	}

	goMod := strings.TrimSpace(goenvOut.String())
	goModContents, err := os.ReadFile(goMod)
	if err != nil {
		log.Fatalf("Could not read go.mod contents: %v\n", err)
	}

	goRootModule := modfile.ModulePath(goModContents)
	if len(goRootModule) == 0 {
		log.Fatalf("Could not detect module name in go.mod file: %s\n", goMod)
	}

	goRootPath, _ := filepath.Split(goMod)

	return goRootModule, goRootPath
}

func getModulePath(suffix string) string {
	_, b, _, _ := runtime.Caller(0)
	return path.Join(filepath.Dir(b), suffix)
}

func getCoqOutputPath(coqPhysicalPath *string, messageName *string) string {
	return path.Join(*coqPhysicalPath, *messageName+"_proof.v")
}

func getGoOutputPath(goPhysicalPath *string, messageName *string) string {
	return path.Join(*goPhysicalPath, strings.ToLower(*messageName)+".go")
}

func getCoqTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName()
	}
	return coqTypeMap[field.GetType()]
}

func generateParameterName(name string) string {
	return strings.ToLower(string(name[0]))
}

func getGoTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return getGoPublicName(field.GetTypeName())
	}
	return goTypeMap[field.GetType()]
}

func getGoPublicName(name string) string {
	return strings.ToUpper(string(name[0])) + name[1:]
}

func getBuiltInMarshalFuncType(field *field) string {
	return marshalTypeMap[field.GetType()]
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
