package util

import (
	"bytes"
	"log"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"runtime"
	"strings"
	"unicode"

	"golang.org/x/mod/modfile"
	"google.golang.org/protobuf/types/descriptorpb"
)

type field = descriptorpb.FieldDescriptorProto
type fieldType = descriptorpb.FieldDescriptorProto_Type

const dirPermissions = 0755
const filePermissions = 0644

var coqTypeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "u32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "u32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "u32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "u64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "u64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "u64",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "message",
	descriptorpb.FieldDescriptorProto_TYPE_BYTES:   "list u8",
	descriptorpb.FieldDescriptorProto_TYPE_STRING:  "string",
}

var goTypeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "uint32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "uint64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "uint64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "uint64",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "message",
	descriptorpb.FieldDescriptorProto_TYPE_BYTES:   "*[]byte",
	descriptorpb.FieldDescriptorProto_TYPE_STRING:  "*string",
}

var marshalTypeMap = map[fieldType]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "Int32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "Int32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "Int32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "Int",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "Int",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "Int",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "message",
	descriptorpb.FieldDescriptorProto_TYPE_BYTES:   "BytesCopy",
	descriptorpb.FieldDescriptorProto_TYPE_STRING:  "BytesCopy",
}

var refTypeMap = map[fieldType]bool{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   false,
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  false,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: false,
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   false,
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  false,
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: false,
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: true,
	descriptorpb.FieldDescriptorProto_TYPE_BYTES:   true,
	descriptorpb.FieldDescriptorProto_TYPE_STRING:  true,
}

// STRING MANIPULATION UTILITIES

func CleanCoqName(goPackage string) string {
	result := strings.Replace(goPackage, ".", "_", -1)
	result = strings.Replace(result, "-", "_", -1)
	result = strings.Replace(result, "/", ".", -1)

	return result
}

var Capitialize = Compose(
	func(s string) []rune { return []rune(s) },
	func(r []rune) string {
		return string(append([]rune{unicode.ToUpper(r[0])}, r[1:]...))
	})

// MAP ACCESSORS & TRANSFORMERS

func GetCoqTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName()
	}
	return coqTypeMap[field.GetType()]
}

func GetGoTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return Capitialize(field.GetTypeName())
	}
	return goTypeMap[field.GetType()]
}

func GetBuiltInMarshalFuncType(field *field) string {
	return marshalTypeMap[field.GetType()]
}

func IsReferenceType(field *field) bool {
	return refTypeMap[field.GetType()]
}

func IsMessageType(field *field) bool {
	return field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE
}

func IsCoqType(field *field, typeStr string) bool {
	return coqTypeMap[field.GetType()] == typeStr
}

// FILESYSTEM UTILITIES

// Searches up the file tree for the go.mod file.
// Returns both the name of the module listed in go.mod and the directory where
// the go.mod is found.
func FindGoModuleName(goDirectory string) (string, string) {
	goenv := exec.Command("go", "env", "GOMOD")
	var goenvOut, goenvErr bytes.Buffer
	goenv.Stderr = &goenvErr
	goenv.Stdout = &goenvOut
	goenv.Dir = goDirectory
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

func GetModulePath(suffix string) string {
	_, b, _, _ := runtime.Caller(0)
	log.Printf(b)
	a, _ := filepath.Split(b)
	_, r := FindGoModuleName(a)
	log.Printf(r)
	return path.Join(filepath.Dir(r), suffix)
}

func GetCoqOutputPath(coqPhysicalPath *string, messageName *string) string {
	return path.Join(*coqPhysicalPath, strings.ToLower(*messageName)+"_proof.v")
}

func GetGoOutputPath(goPhysicalPath *string, messageName *string) string {
	lowerMessage := strings.ToLower(*messageName)
	return path.Join(*goPhysicalPath, lowerMessage+"_gk", lowerMessage+"_gk.go")
}

func GetGooseOutputPath(gooseOutput *string, goosePackagePath string) string {
	components := strings.Split(CleanCoqName(goosePackagePath), ".")
	components = append([]string{*gooseOutput}, components...)
	return filepath.Join(components...) + ".v"
}

func CreateOutputDirectories(gooseOutput *string, coqPhysicalPath *string, goOutputPath *string) {
	if gooseOutput != nil {
		os.MkdirAll(*gooseOutput, dirPermissions)
	}
	if coqPhysicalPath != nil {

		os.MkdirAll(*coqPhysicalPath, dirPermissions)
	}
	if goOutputPath != nil {

		os.MkdirAll(*goOutputPath, dirPermissions)
	}
}

func OpenGrackleFile(path *string) *os.File {
	os.MkdirAll(filepath.Dir(*path), dirPermissions)
	file, err := os.OpenFile(*path, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, filePermissions)
	if err != nil {
		log.Fatalf("Could not open output file: %v\n", err)
	}

	return file
}

// FUNCTIONAL UTILITIES

func Compose[A any, B any, C any](f func(A) B, g func(B) C) func(A) C {
	return func(a A) C {
		return g(f(a))
	}
}

func Filter[T any](slice []T, f func(T) bool) []T {
	var n []T
	for _, e := range slice {
		if f(e) {
			n = append(n, e)
		}
	}
	return n
}
