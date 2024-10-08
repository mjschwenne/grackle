package main

import (
	"log"
	"os"
	"path"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"

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
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "int32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "int64",
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
	currentDir, err := filepath.Abs(goOutputPath)
	if err != nil {
		log.Fatalf("Could not resolve relative path: %v\n", err)
	}

	for {
		var goMod = path.Join(currentDir, "go.mod")
		files, err := filepath.Glob(goMod)
		if err != nil {
			log.Fatalf("Error finding parent go.mod: %v\n", err)
		}
		if len(files) > 1 {
			log.Fatalf("Error: Too many go.mod files found")
		} else if len(files) == 1 {
			regex := regexp.MustCompile(`(?m)^module (?<mod>[^\s]+)$`)
			goModContents, err := os.ReadFile(goMod)
			// Do y'all ever feel like you need a monad to handle all of these
			// functions which return an error?
			if err != nil {
				log.Fatalf("Could not read go.mod contents: %v\n", err)
			}
			return regex.FindStringSubmatch(string(goModContents))[1], currentDir
		} else {
			// Peel off the trailing '/' and cut off the next directory
			currentDir, _ = filepath.Split(currentDir[:len(currentDir)-1])
			// Trying to search above the file system root.
			// This check might not work on windows but I hope it does on mac
			// I don't have a mac so I can't really test
			if currentDir == "" {
				log.Fatalf("Could not find go.mod.\n")
			}
		}
	}
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
