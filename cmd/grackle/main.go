package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/mjschwenne/grackle"
)

func main() {
	// Parse command line arguments
	var gooseOutputPath = flag.String("goose-output", "", "Directory to write the goose output")
	var coqLogicalPath = flag.String("rocq-logical-path", "", "Logical path to import the marshal proofs from")
	var coqPhysicalPath = flag.String("rocq-physical-path", "", "Physical output path for rocq proofs")
	var proofGenPath = flag.String("proofgen-path", "", "Physical output path for proofgen files")
	var debug = flag.Bool("debug", false, "Output all generated code to stdout")
	var goOutputPath = flag.String("go-output-path", "", "Physical path to output go code into")
	var goPackage = flag.String("go-package", "", "Fully qualified root package for the output packages")

	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: grackle [options] <path to protobuf files>")
		flag.PrintDefaults()
	}

	flag.Parse()

	*goPackage = strings.TrimRight(*goPackage, "/")

	var protoDir = flag.Args()
	if len(protoDir) != 1 {
		fmt.Println("Usage: grackle [options] proto-directory ...")
		os.Exit(1)
	}

	// Allow the user to write to stdout if they want...
	var capture io.Writer
	if *debug {
		capture = os.Stdout
	} else {
		capture = nil
	}

	grackle.Grackle(&protoDir[0], gooseOutputPath, coqLogicalPath, coqPhysicalPath, proofGenPath, goOutputPath, goPackage, capture)
}
