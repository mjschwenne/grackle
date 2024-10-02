package main

import (
	"path"
	"path/filepath"
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

var refTypeMap = map[fieldType]bool{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   false,
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  false,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: false,
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   false,
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  false,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: false,
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: true,
}

func getModulePath(suffix string) string {
	_, b, _, _ := runtime.Caller(0)
	return path.Join(filepath.Dir(b), suffix)
}

func getCoqOutputPath(coqPhysicalPath *string, messageName *string) string {
	return path.Join(*coqPhysicalPath, *messageName+"_proof.v")
}

func getCoqTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName()
	}
	return coqTypeMap[field.GetType()]
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
