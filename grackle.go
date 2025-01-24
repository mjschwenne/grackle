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
	"regexp"
	"slices"
	"strconv"
	"strings"
	"text/template"

	"github.com/goose-lang/goose"
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
		"protoType":      util.GetProtoTypeName,
		"coqType":        util.GetCoqTypeName,
		"isExtValType":   util.IsExternalValType,
		"isMessage":      util.IsMessageType,
		"isCoqType":      util.IsCoqType,
		"isGoType":       util.IsGoType,
		"isSliceType":    util.IsSliceType,
		"isRepeatedType": util.IsRepeatedType,
		"extValFields":   func(fields []*field) []*field { return util.Filter(fields, util.IsExternalValType) },
		"messageFields":  func(fields []*field) []*field { return util.Filter(fields, util.IsMessageType) },
		"notMsgFields": func(fields []*field) []*field {
			return util.Filter(fields, func(f *field) bool { return !util.IsMessageType(f) })
		},
		"allNestedMsgs": func(m string) []string { return util.GetAllNestedMessages(m, []string{}, msgDict) },
		"sliceFields":   func(fields []*field) []*field { return util.Filter(fields, util.IsSliceType) },
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
		"callTemplate": func(name string, data interface{}) (ret string, err error) {
			buf := bytes.NewBuffer([]byte{})
			err = tmpl.ExecuteTemplate(buf, name, data)
			ret = buf.String()
			return
		},
		"dict": func(values ...interface{}) (map[string]interface{}, error) {
			if len(values)%2 != 0 {
				return nil, errors.New("invalid dict call")
			}
			dict := make(map[string]interface{}, len(values)/2)
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

// Override options with file-specific values if needed
func getFileOptions(file *descriptorpb.FileDescriptorProto, gooseOutput *string, coqLogicalPath *string, coqPhysicalPath *string, goOutputPath *string, goPackage *string) *fileParams {
	const COQ_LOGICAL_PATH_FIELD_TAG = 50621
	const COQ_PHYSICAL_PATH_FIELD_TAG = 50622
	const GOOSE_OUTPUT_PATH = 50623

	var fileCoqLogicalPath = coqLogicalPath
	var fileCoqPhysicalPath = coqPhysicalPath
	var fileGooseOutput = gooseOutput

	if file.GetOptions() != nil {
		regex := regexp.MustCompile(`(?<field>\d+):"(?<value>[^"]+)"`)
		for _, match := range regex.FindAllStringSubmatch(file.GetOptions().String(), -1) {
			field, _ := strconv.Atoi(match[1])
			switch field {
			case COQ_LOGICAL_PATH_FIELD_TAG:
				fileCoqLogicalPath = &match[2]
			case COQ_PHYSICAL_PATH_FIELD_TAG:
				fileCoqPhysicalPath = &match[2]
			}
		}
	}

	return &fileParams{
		GooseOutput:     fileGooseOutput,
		CoqLogicalPath:  fileCoqLogicalPath,
		CoqPhysicalPath: fileCoqPhysicalPath,
		GoOutputPath:    goOutputPath,
		GoPackage:       goPackage,
	}
}

func getMessageOptions(message *descriptorpb.DescriptorProto, fileOpts *fileParams) messageParams {
	var fields []*field
	var nested []string
	for _, f := range message.GetField() {
		if f.GetType() == descriptorpb.FieldDescriptorProto_TYPE_MESSAGE {
			realName := (f.GetTypeName())[1:]
			f.TypeName = &realName
			if !slices.Contains(nested, realName) {
				nested = append(nested, realName)
			}
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
		NestedMessages:  nested,
		Fields:          fields,
	}

	return messageOpts
}

func gooseTranslate(gooseOutput *string, goRoot string, goDirectory string) {
	gooseConfig := goose.TranslationConfig{TypeCheck: false, AddSourceFileComments: false, SkipInterfaces: false}
	goAbs, err := filepath.Abs(goDirectory)
	gooseFiles, gooseErrs, err := gooseConfig.TranslatePackages(goRoot, goAbs)
	if err != nil {
		log.Fatalf("Could not generate goose code: %v\n", err)
	}

	for _, ge := range gooseErrs {
		if ge != nil {
			log.Printf("Warning: Goose error: %v\n", ge)
		}
	}

	for _, gf := range gooseFiles {
		gooseFilePath := util.GetGooseOutputPath(gooseOutput, gf.PkgPath)
		gooseFile := util.OpenGrackleFile(&gooseFilePath)
		gf.Write(gooseFile)
		gooseFile.Close()
	}
}

func Grackle(protoDir *string, gooseOutput *string, coqLogicalPath *string, coqPhysicalPath *string, goOutputPath *string, goPackage *string, debug io.Writer) {
	descriptorSet := generateDescirptor(protoDir)
	tmpl := setupTemplates(descriptorSet)
	util.CreateOutputDirectories(gooseOutput, coqPhysicalPath, goOutputPath)

	goFiles := make([]*string, 0, 10)
	for _, file := range descriptorSet.File {
		fileOpts := getFileOptions(file, gooseOutput, coqLogicalPath, coqPhysicalPath, goOutputPath, goPackage)
		for _, enum := range file.EnumType {
			// log.Printf("Found enum: %s\n", enum.GetName())
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
					log.Printf(goBuffer.String())
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
			msg := getMessageOptions(message, fileOpts)
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
					log.Printf(goBuffer.String())
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
				_, goRoot := util.FindGoModuleName(*goOutputPath)
				gooseTranslate(gooseOutput, goRoot, filepath.Dir(*msg.GoPhysicalPath))
			}
		}
	}
}
