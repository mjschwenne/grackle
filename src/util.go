package grackle

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

func cleanCoqName(goPackage string) string {
	result := strings.Replace(goPackage, ".", "_", -1)
	result = strings.Replace(result, "/", ".", -1)

	return result
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
	lowerMessage := strings.ToLower(*messageName)
	return path.Join(*goPhysicalPath, lowerMessage, lowerMessage+".go")
}

func createOutputDirectories(gooseOutput *string, coqPhysicalPath *string, goOutputPath *string) {
	os.MkdirAll(*gooseOutput, dirPermissions)
	os.MkdirAll(*coqPhysicalPath, dirPermissions)
	os.MkdirAll(*goOutputPath, dirPermissions)
}

func openGrackleFile(path *string) *os.File {
	os.MkdirAll(filepath.Dir(*path), dirPermissions)
	file, err := os.OpenFile(*path, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, filePermissions)
	if err != nil {
		log.Fatalf("Could not open output file: %v\n", err)
	}

	return file
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
		return capitialize(field.GetTypeName())
	}
	return goTypeMap[field.GetType()]
}

func getBuiltInMarshalFuncType(field *field) string {
	return marshalTypeMap[field.GetType()]
}

func compose[A any, B any, C any](f func(A) B, g func(B) C) func(A) C {
	return func(a A) C {
		return g(f(a))
	}
}

var capitialize = compose(
	func(s string) []rune { return []rune(s) },
	func(r []rune) string {
		return string(append([]rune{unicode.ToUpper(r[0])}, r[1:]...))
	})

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
