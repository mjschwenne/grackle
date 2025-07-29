package grackle

import (
	"bytes"
	"embed"
	"errors"
	"fmt"
	"go/format"
	"io"
	"io/fs"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"text/template"

	"github.com/goose-lang/goose"
	"github.com/goose-lang/goose/proofgen"
	pg "github.com/goose-lang/goose/util"
	"github.com/mjschwenne/grackle/internal/util"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

type field = descriptorpb.FieldDescriptorProto
type fieldType = descriptorpb.FieldDescriptorProto_Type

type fileParams struct {
	GooseOutput     *string
	CoqLogicalPath  *string
	CoqPhysicalPath *string
	GoOutputPath    *string
	GoPackage       *string
}

type messageParams struct {
	Name            *string
	GooseOutput     *string
	CoqLogicalPath  *string
	CoqPhysicalPath *string
	GoPhysicalPath  *string
	GoPackage       *string
	Simple          bool
	NestedMessages  []string
	Fields          []*field
	MsgMap          map[string]*descriptorpb.DescriptorProto
}

//go:embed internal/templates
var tmplFS embed.FS

func generateDescirptor(protoDir *string) *descriptorpb.FileDescriptorSet {
	absProtoDir, err := filepath.Abs(*protoDir)
	if err != nil {
		log.Fatalf("Could not locate directory '%s': %v\n", *protoDir, err)
	}

	// Find the proto files in the protoDir
	var protoFiles []string
	filepath.WalkDir(*protoDir, func(path string, d fs.DirEntry, err error) error {
		relativePath, err := filepath.Rel(*protoDir, path)
		if err != nil {
			return err
		}

		if !d.Type().IsDir() && filepath.Ext(path) == ".proto" {
			protoFiles = append(protoFiles, relativePath)
		}

		return nil
	})
	// Generate proto descriptor in temp file
	descirptorFile, err := os.CreateTemp("", "grackle-")
	if err != nil {
		log.Fatalf("Failed to create temporary descriptor file: %v", err)
	}
	descirptorName := descirptorFile.Name()

	// Remove descriptor file at the end of the program
	defer descirptorFile.Close()
	defer os.Remove(descirptorName)

	protoc := exec.Command("protoc", append([]string{"--descriptor_set_out=" + descirptorName, "--proto_path=."}, protoFiles...)...)
	var protocErr bytes.Buffer
	protoc.Stderr = &protocErr
	protoc.Dir = absProtoDir
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

	return &fileDescriptorSet
}

func setupTemplates(files *descriptorpb.FileDescriptorSet) *template.Template {
	msgDict := map[string]*descriptorpb.DescriptorProto{}

	for _, file := range files.GetFile() {
		for _, msg := range file.GetMessageType() {
			msgDict[msg.GetName()] = msg
		}
	}

	tmpl := template.New("grackle").Delims("<<", ">>")
	funcMap := template.FuncMap{
		"protoType":       util.GetProtoTypeName,
		"coqType":         util.GetCoqTypeName,
		"isExtValType":    util.IsExternalValType,
		"isMessage":       util.IsMessageType,
		"isCoqType":       util.IsCoqType,
		"isGoType":        util.IsGoType,
		"isSliceType":     util.IsSliceType,
		"isPredSliceType": util.IsPredSliceType,
		"isRepeatedType":  util.IsRepeatedType,
		"extValFields":    func(fields []*field) []*field { return util.Filter(fields, util.IsExternalValType) },
		"messageFields":   func(fields []*field) []*field { return util.Filter(fields, util.IsMessageType) },
		"notMsgFields": func(fields []*field) []*field {
			return util.Filter(fields, func(f *field) bool { return !util.IsMessageType(f) })
		},
		"extEncFields": func(fields []*field) []*field {
			return util.Filter(fields, func(f *field) bool { return util.IsMessageType(f) || util.IsRepeatedType(f) })
		},
		"allNestedMsgs":  func(m string) []string { return util.GetAllNestedMessages(m, []string{}, msgDict) },
		"sliceFields":    func(fields []*field) []*field { return util.Filter(fields, util.IsSliceType) },
		"repeatedFields": func(fields []*field) []*field { return util.Filter(fields, util.IsRepeatedType) },
		"sliceFieldsRecursive": func(m string) []*field {
			return util.GetFieldsRecursive(m, func(fields []*field) []*field { return util.Filter(fields, util.IsSliceType) }, msgDict)
		},
		"filterByCoqType": func(fields []*field, typeStr string) []*field {
			return util.Filter(fields, func(f *field) bool { return util.IsCoqType(f, typeStr) })
		},
		"filterByGoType": func(fields []*field, typeStr string) []*field {
			return util.Filter(fields, func(f *field) bool { return util.IsGoType(f, typeStr) })
		},
		"join":          func(sep string, s ...string) string { return strings.Join(s, sep) },
		"indent":        util.Indent,
		"trunc":         util.Trunc,
		"lower":         strings.ToLower,
		"pred":          func(i int) int { return i - 1 },
		"succ":          func(i int) int { return i + 1 },
		"goType":        util.GetGoTypeName,
		"param":         func(s string) string { return strings.ToLower(string(s[0])) },
		"marshalType":   util.GetBuiltInMarshalFuncType,
		"goModuleName":  util.GetGoModuleName,
		"coqModuleName": util.GetCoqModuleName,
		"valFunc":       func(f *field) string { return util.GetValFunc(f, msgDict) },
		"hasValFunc":    func(m string) bool { return util.HasValFunc(m, msgDict) },
		"cleanCoqName":  util.CleanCoqName,
		"goName":        util.Capitialize,
		// This is a bit of a hack to let me call templates with dynamic names
		// It requires tmpl in the closure of the function, so the inline definition
		// makes the most sense
		"callTemplate": func(name string, data any) (ret string, err error) {
			buf := bytes.NewBuffer([]byte{})
			err = tmpl.ExecuteTemplate(buf, name, data)
			ret = buf.String()
			return
		},
		"dict": func(values ...any) (map[string]any, error) {
			if len(values)%2 != 0 {
				return nil, errors.New("invalid dict call")
			}
			dict := make(map[string]any, len(values)/2)
			for i := 0; i < len(values); i += 2 {
				key, ok := values[i].(string)
				if !ok {
					return nil, errors.New("dict keys must be strings")
				}
				dict[key] = values[i+1]
			}
			return dict, nil
		},
		"fetchMsg": func(s string) *descriptorpb.DescriptorProto { return msgDict[s] },
	}
	tmpl, err := tmpl.Funcs(funcMap).ParseFS(tmplFS, "internal/templates/*.tmpl")
	if err != nil {
		panic(err)
	}

	return tmpl
}

func generateMsg(message *descriptorpb.DescriptorProto, fileOpts *fileParams) messageParams {
	// A message is simple if it has no repeated fields (or enums/oneof?)
	simple := true
	var fields []*field
	var nested []string
	for _, f := range message.GetField() {
		if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE ||
			f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_ENUM {
			realName := (f.GetTypeName())[1:]
			f.TypeName = &realName
			if !slices.Contains(nested, realName) {
				nested = append(nested, realName)
			}
			// } else if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_ENUM &&
			// 	!slices.Contains(nested, f.GetTypeName()) {
			// 	nested = append(nested, f.GetTypeName())
		}
		if util.IsRepeatedType(f) || util.IsCoqType(f, "u8") {
			simple = false
		}
		fields = append(fields, f)
	}

	coqOutputPath := util.GetCoqOutputPath(fileOpts.CoqPhysicalPath, message.Name)
	goOutputPath := util.GetGoOutputPath(fileOpts.GoOutputPath, message.Name)
	messageOpts := messageParams{
		Name:            message.Name,
		GooseOutput:     fileOpts.GooseOutput,
		CoqLogicalPath:  fileOpts.CoqLogicalPath,
		CoqPhysicalPath: &coqOutputPath,
		GoPhysicalPath:  &goOutputPath,
		GoPackage:       fileOpts.GoPackage,
		Simple:          simple,
		NestedMessages:  nested,
		Fields:          fields,
	}

	return messageOpts
}

func gooseTranslate(gooseOutput *string, proofGenPath *string, goRoot string, goDirectory string) {
	goAbs, err := filepath.Abs(goDirectory)
	gooseFiles, gooseErrs, err := goose.TranslatePackages(goRoot, goAbs)
	if err != nil {
		log.Fatalf("Could not generate goose code: %v\n", err)
	}

	for _, ge := range gooseErrs {
		if ge != nil {
			log.Printf("Warning: Goose error: %v\n", ge)
		}
	}

	if proofGenPath != nil {
		pg.Translate(proofgen.Package, []string{}, *proofGenPath, goAbs, *gooseOutput)
	}

	for _, gf := range gooseFiles {
		gooseFilePath := util.GetGooseOutputPath(gooseOutput, gf.PkgPath)
		gooseFile := util.OpenGrackleFile(&gooseFilePath)
		gf.Write(gooseFile)
		gooseFile.Close()
	}
}

func Grackle(protoDir *string,
	gooseOutput *string,
	coqLogicalPath *string,
	coqPhysicalPath *string,
	proofGenOutput *string,
	goOutputPath *string,
	goPackage *string,
	debug io.Writer) {

	descriptorSet := generateDescirptor(protoDir)
	tmpl := setupTemplates(descriptorSet)
	util.CreateOutputDirectories(gooseOutput, coqPhysicalPath, goOutputPath)

	goFiles := make([]*string, 0, 10)
	for _, file := range descriptorSet.File {
		fileOpts := &fileParams{
			GooseOutput:     gooseOutput,
			CoqLogicalPath:  coqLogicalPath,
			CoqPhysicalPath: coqPhysicalPath,
			GoOutputPath:    goOutputPath,
			GoPackage:       goPackage,
		}
		for _, enum := range file.EnumType {
			var goOut io.Writer
			goPhysicalPath := util.GetGoOutputPath(goOutputPath, enum.Name)
			if *goOutputPath != "" {
				if debug != nil {
					goOut = debug
					fmt.Fprintf(debug, "--- Start: %s ---\n", goPhysicalPath)
				} else {
					goOut = util.OpenGrackleFile(&goPhysicalPath)
					goFiles = append(goFiles, &goPhysicalPath)
				}
				// Write to a buffer, then format
				// The buffer may seem large, but it is only 1 MB
				goBuffer := bytes.NewBuffer(make([]byte, 0, 1000000))
				err := tmpl.ExecuteTemplate(goBuffer, "go_enum.tmpl", enum)
				if err != nil {
					log.Fatalf("Error generating go code: %v\n", err)
				}

				formattedGo, err := format.Source(goBuffer.Bytes())
				if err != nil {
					log.Printf("Could not format code:\n%s\n", goBuffer.String())
					log.Fatalf("Error formatting go code: %v\n", err)
				}

				_, err = goOut.Write(formattedGo)
				if err != nil {
					log.Fatalf("Error writing go code: %v\n", err)
				}

				if debug != nil {
					fmt.Fprintf(debug, "--- End: %s ---\n", goPhysicalPath)
				}
			}
		}
		for _, message := range file.MessageType {
			msg := generateMsg(message, fileOpts)
			var coqOut io.Writer
			var goOut io.Writer

			if *coqPhysicalPath != "" {
				if debug != nil {
					coqOut = debug
					fmt.Fprintf(debug, "--- Begin: %s ---\n", *msg.CoqPhysicalPath)
				} else {
					coqOut = util.OpenGrackleFile(msg.CoqPhysicalPath)
				}
				err := tmpl.ExecuteTemplate(coqOut, "coq_proof.tmpl", msg)

				if err != nil {
					log.Fatalf("Error generating coq code: %v\n", err)
				}
				if debug != nil {
					fmt.Fprintf(debug, "--- End: %s ---\n", *msg.CoqPhysicalPath)
				}
			}

			if *goOutputPath != "" {
				if debug != nil {
					goOut = debug
					fmt.Fprintf(debug, "--- Start: %s ---\n", *msg.GoPhysicalPath)
				} else {
					goOut = util.OpenGrackleFile(msg.GoPhysicalPath)
					goFiles = append(goFiles, msg.GoPhysicalPath)
				}
				// Write to a buffer, then format
				// The buffer may seem large, but it is only 1 MB
				goBuffer := bytes.NewBuffer(make([]byte, 0, 1000000))
				err := tmpl.ExecuteTemplate(goBuffer, "go_file.tmpl", msg)
				if err != nil {
					log.Fatalf("Error generating go code: %v\n", err)
				}

				formattedGo, err := format.Source(goBuffer.Bytes())
				if err != nil {
					log.Printf("Could not format code:\n%s\n", goBuffer.String())
					log.Fatalf("Error formatting go code: %v\n", err)
				}

				_, err = goOut.Write(formattedGo)
				if err != nil {
					log.Fatalf("Error writing go code: %v\n", err)
				}

				if debug != nil {
					fmt.Fprintf(debug, "--- End: %s ---\n", *msg.GoPhysicalPath)
				}
			}

			// Goose Translation, but only if the user wants and we have real go output
			if debug == nil && *gooseOutput != "" && *goOutputPath != "" {
				if *proofGenOutput == "" {
					log.Printf("Warning: proofgen output path not set, skipping proofgen generation!\n")
				}
				_, goRoot := util.FindGoModuleName(*goOutputPath)
				gooseTranslate(gooseOutput, proofGenOutput, goRoot, filepath.Dir(*msg.GoPhysicalPath))
			}
		}
	}
}
