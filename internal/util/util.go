package util

import (
	"bytes"
	"log"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
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
	ProtoType   string // Holds the string name of this type to unify names across languages
	CoqType     string // Holds the corresponding coq type
	GoType      string // Holds the corresponding go type
	MarshalType string // Holds the name of the function in tchajed/marshal which operates on this type
	ValType     bool   // Holds whether this type uses an external value in the coq proof
	SliceType   bool   // Holds whether this type is actually a list of values
	ToValFunc   string // Holds how to take a coq type to a value, i.e. #(...) or #(str ...)
}

var TypeMap = map[fieldType]TypeData{
	descriptorpb.FieldDescriptorProto_TYPE_INT32: {
		ProtoType:   "int32",
		CoqType:     "u32",
		GoType:      "uint32",
		MarshalType: "Int32",
	},
	descriptorpb.FieldDescriptorProto_TYPE_UINT32: {
		ProtoType:   "int32",
		CoqType:     "u32",
		GoType:      "uint32",
		MarshalType: "Int32",
	},
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: {
		ProtoType:   "int32",
		CoqType:     "u32",
		GoType:      "uint32",
		MarshalType: "Int32",
	},
	descriptorpb.FieldDescriptorProto_TYPE_INT64: {
		ProtoType:   "int64",
		CoqType:     "u64",
		GoType:      "uint64",
		MarshalType: "Int",
	},
	descriptorpb.FieldDescriptorProto_TYPE_UINT64: {
		ProtoType:   "int64",
		CoqType:     "u64",
		GoType:      "uint64",
		MarshalType: "Int",
	},
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: {
		ProtoType:   "int64",
		CoqType:     "u64",
		GoType:      "uint64",
		MarshalType: "Int",
	},
	descriptorpb.FieldDescriptorProto_TYPE_BOOL: {
		ProtoType:   "bool",
		CoqType:     "bool",
		GoType:      "bool",
		MarshalType: "Bool",
	},
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: {
		ProtoType:   "message",
		CoqType:     "message",
		GoType:      "message",
		MarshalType: "message",
		ValType:     true,
	},
	descriptorpb.FieldDescriptorProto_TYPE_BYTES: {
		ProtoType:   "bytes",
		CoqType:     "list u8",
		GoType:      "byte",
		MarshalType: "Bytes",
		SliceType:   true,
		ToValFunc:   "slice_val",
	},
	descriptorpb.FieldDescriptorProto_TYPE_STRING: {
		ProtoType:   "string",
		CoqType:     "byte_string",
		GoType:      "string",
		MarshalType: "String", // Not technically true, but it helps on the coq side
		SliceType:   false,    // Not really true, but it all works out.
		ToValFunc:   "str",
	},
	descriptorpb.FieldDescriptorProto_TYPE_ENUM: {
		ProtoType:   "enum",
		CoqType:     "enum",
		GoType:      "enum",
		MarshalType: "enum",
	},
}

var LabelMap = map[descriptorpb.FieldDescriptorProto_Label]TypeData{
	descriptorpb.FieldDescriptorProto_LABEL_REPEATED: {
		ProtoType:   "repeated",
		CoqType:     "list",
		GoType:      "[]",
		MarshalType: "SliceLenPrefix",
		SliceType:   true,
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

// Takes the first (or removes the last if c is negative) characters from s
func Trunc(c int, s string) string {
	if c < 0 && len(s)+c > 0 {
		return s[:len(s)+c]
	}
	if c >= 0 && len(s) > c {
		return s[:c]
	}
	return s
}

// Replace the beginning of each line with n spaces
func Indent(n int, s string) string {
	spacer := strings.Repeat(" ", n)
	regex := regexp.MustCompile(`(?m)^`)
	return regex.ReplaceAllString(s, spacer)
}

// MAP ACCESSORS & TRANSFORMERS

func GetProtoTypeName(field *field) string {
	return TypeMap[field.GetType()].ProtoType
}

func GetCoqTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName() + ".C"
	}
	return TypeMap[field.GetType()].CoqType
}

func GetGoTypeName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return strings.ToLower(field.GetTypeName()) + "_gk.S"
	}
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_ENUM {
		return strings.ToLower(field.GetTypeName()[1:]) + "_gk.E"
	}
	return TypeMap[field.GetType()].GoType
}

func GetGoModuleName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return strings.ToLower(field.GetTypeName()) + "_gk"
	}

	return ""
}

func GetCoqModuleName(field *field) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
		return field.GetTypeName()
	}

	return ""
}

func GetBuiltInMarshalFuncType(field *field) string {
	return TypeMap[field.GetType()].MarshalType
}

func GetAllNestedMessages(msgName string, nested []string, msgMap map[string]*descriptorpb.DescriptorProto) []string {
	msg := msgMap[msgName]
	for _, f := range msg.GetField() {
		name := f.GetTypeName()
		if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE && !slices.Contains(nested, name) {
			nested = append(nested, name)
			nested = GetAllNestedMessages(name, nested, msgMap)
		}
	}
	return nested
}

func GetFieldsRecursive(msgName string, fieldFunc func(f []*field) []*field, msgMap map[string]*descriptorpb.DescriptorProto) []*field {
	nested := GetAllNestedMessages(msgName, []string{msgName}, msgMap)
	resultFields := []*field{}
	for _, m := range nested {
		resultFields = append(resultFields, fieldFunc(msgMap[m].GetField())...)
	}
	return resultFields
}

func HasValFunc(msgName string, msgMap map[string]*descriptorpb.DescriptorProto) bool {
	msg := msgMap[msgName]
	var nested []string
	for _, f := range msg.GetField() {
		if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
			realName := f.GetTypeName()
			if slices.Contains(nested, realName) {
				continue
			} else if HasValFunc(realName, msgMap) {
				nested = append(nested, realName)
			} else {
				return false
			}
		}
		if IsSliceType(f) {
			return false
		}
	}
	return true
}

func GetValFunc(field *field, msgMap map[string]*descriptorpb.DescriptorProto) string {
	if field.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE && HasValFunc(field.GetTypeName(), msgMap) {
		return field.GetTypeName() + ".to_val'"
	}
	return TypeMap[field.GetType()].ToValFunc
}

func IsRepeatedType(field *field) bool {
	return *field.Label == descriptorpb.FieldDescriptorProto_LABEL_REPEATED
}

func IsExternalValType(field *field) bool {
	return TypeMap[field.GetType()].ValType
}

func IsSliceType(field *field) bool {
	return TypeMap[field.GetType()].SliceType || IsRepeatedType(field)
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
	return path.Join(*coqPhysicalPath, strings.ToLower(*messageName)+"_proof_gk.v")
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
