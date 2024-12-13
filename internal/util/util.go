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

const DirPermissions = 0755
const FilePermissions = 0644

type TypeData struct {
	CoqType     string
	GoType      string
	MarshalType string
	RefType     bool
}

var TypeMap = map[fieldType]TypeData{
	descriptorpb.FieldDescriptorProto_TYPE_INT32: {
		CoqType:     "u32",
		GoType:      "uint32",
		MarshalType: "Int32",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_UINT32: {
		CoqType:     "u32",
		GoType:      "uint32",
		MarshalType: "Int32",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: {
		CoqType:     "u32",
		GoType:      "uint32",
		MarshalType: "Int32",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_INT64: {
		CoqType:     "u64",
		GoType:      "uint64",
		MarshalType: "Int",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_UINT64: {
		CoqType:     "u64",
		GoType:      "uint64",
		MarshalType: "Int",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: {
		CoqType:     "u64",
		GoType:      "uint64",
		MarshalType: "Int",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: {
		CoqType:     "message",
		GoType:      "message",
		MarshalType: "message",
		RefType:     true,
	},
	descriptorpb.FieldDescriptorProto_TYPE_BYTES: {
		CoqType:     "list u8",
		GoType:      "[]byte",
		MarshalType: "Bytes",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_STRING: {
		CoqType:     "string",
		GoType:      "string",
		MarshalType: "Bytes",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_BOOL: {
		CoqType:     "bool",
		GoType:      "bool",
		MarshalType: "Bool",
		RefType:     false,
	},
	descriptorpb.FieldDescriptorProto_TYPE_ENUM: {
		CoqType:     "enum",
		GoType:      "enum",
		MarshalType: "enum",
		RefType:     false,
	},
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
	return TypeMap[field.GetType()].CoqType
}

func GetGoTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return Capitialize(field.GetTypeName())
	}
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_ENUM {
		return strings.ToLower(field.GetTypeName()[1:]) + "_gk.E"
	}
	return TypeMap[field.GetType()].GoType
}

func GetBuiltInMarshalFuncType(field *field) string {
	return TypeMap[field.GetType()].MarshalType
}

func IsReferenceType(field *field) bool {
	return TypeMap[field.GetType()].RefType
}

func IsMessageType(field *field) bool {
	return field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE
}

func IsCoqType(field *field, typeStr string) bool {
	// Supports disjunctions via |
	types := strings.Split(typeStr, "|")
	for _, t := range types {
		if TypeMap[field.GetType()].CoqType == t {
			return true
		}
	}
	return false
}

func IsGoType(field *field, typeStr string) bool {
	// Supports disjunctions via |
	types := strings.Split(typeStr, "|")
	for _, t := range types {
		if TypeMap[field.GetType()].GoType == t {
			return true
		}
	}
	return false
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
	if *gooseOutput != "" {
		os.MkdirAll(*gooseOutput, DirPermissions)
	}
	if *coqPhysicalPath != "" {

		os.MkdirAll(*coqPhysicalPath, DirPermissions)
	}
	if *goOutputPath != "" {

		os.MkdirAll(*goOutputPath, DirPermissions)
	}
}

func OpenGrackleFile(path *string) *os.File {
	os.MkdirAll(filepath.Dir(*path), DirPermissions)
	file, err := os.OpenFile(*path, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, FilePermissions)
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
