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
	var coqLogicalPath = flag.String("coq-logical-path", "", "Logical path to import the marshal proofs from")
	var coqPhysicalPath = flag.String("coq-physical-path", "", "Physical output path for coq proofs")
	var debug = flag.Bool("debug", false, "Output all generated code to stdout")
	var goOutputPath = flag.String("go-output-path", "", "Physical path to output go code into")
	var goPackage = flag.String("go-package", "", "Fully qualified root package for the output packages")
	flag.Parse()

	if len(*gooseOutputPath) < 1 {
		fmt.Println("goose-output path must be at least 1 character long!")
		os.Exit(1)
	}

	if len(*coqLogicalPath) < 1 {
		fmt.Println("coq-logical-path must be at least 1 character long!")
		os.Exit(1)
	}

	if len(*goOutputPath) < 1 {
		fmt.Println("go-output-path must be at least 1 character long!")
		os.Exit(1)
	}

	if len(*goPackage) < 1 {
		fmt.Println("go-package must be at least 1 character long!")
		os.Exit(1)
	}
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

	grackle.Grackle(&protoDir[0], gooseOutputPath, coqLogicalPath, coqPhysicalPath, goOutputPath, goPackage, capture)
}
