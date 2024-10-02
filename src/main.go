package main

import (
	"flag"
	"fmt"
	"io"
	"os"
)

func main() {
	// Parse command line arguments
	var gooseOutputPath = flag.String("goose-output", "", "Directory to write the goose output")
	var coqLogicalPath = flag.String("coq-logical-path", "", "Logical path to import the marshal proofs from")
	var coqPhysicalPath = flag.String("coq-physical-path", "", "Physical output path for coq proofs")
	var debug = flag.Bool("debug", false, "Output all generated code to stdout")
	// var goOutputPath = flag.String("go-output-path", "", "Physical path to output go code into")
	// var goPackageName = flag.String("go-package-name", "", "Name for the autogrenerated go package")
	flag.Parse()

	var protoFiles = flag.Args()
	if len(protoFiles) < 1 {
		fmt.Println("Usage: grackle [options] proto-files ...")
		os.Exit(1)
	}

	// Allow the user to write to stdout if they want...
	var capture io.Writer
	if *debug {
		capture = os.Stdout
	} else {
		capture = nil
	}

	grackle(&protoFiles, gooseOutputPath, coqLogicalPath, coqPhysicalPath, capture)
}
