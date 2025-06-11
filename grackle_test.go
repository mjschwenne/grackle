package grackle

import (
	"bufio"
	"bytes"
	"testing"

	"github.com/mjschwenne/grackle/internal/util"
	"gotest.tools/v3/golden"
)

func TestGetCoqOutput(t *testing.T) {
	logicalPath := "example"
	name := "Event"
	actual := util.GetCoqOutputPath(&logicalPath, &name)
	if actual != "example/event_proof_gk.v" {
		t.Errorf("Wanted `example/event_proof_gk.v`, got %v\n", actual)
	}
}

func TestCalendarExample(t *testing.T) {
	grackleBuffer := bytes.NewBuffer(make([]byte, 0, 10000))
	grackleOutput := bufio.NewWriter(grackleBuffer)
	protoFiles := "testdata/proto/calendar"
	gooseOutput := "testdata/out/goose"
	coqLogicalPath := "Grackle.test"
	coqPhysicalPath := "testdata/out/coq"
	goOutputPath := "testdata/out/go"
	goPackage := "github.com/mjschwenne/grackle/testdata/out/go"
	Grackle(&protoFiles, &gooseOutput, &coqLogicalPath, &coqPhysicalPath, nil, &goOutputPath, &goPackage, grackleOutput)
	grackleOutput.Flush()
	golden.Assert(t, grackleBuffer.String(), "golden/calendar.golden")
}

func TestCompleteExample(t *testing.T) {
	grackleBuffer := bytes.NewBuffer(make([]byte, 0, 10000))
	grackleOutput := bufio.NewWriter(grackleBuffer)
	protoFiles := "testdata/proto/complete/"
	gooseOutput := "testdata/out/goose"
	coqLogicalPath := "Grackle.test"
	coqPhysicalPath := "testdata/out/coq"
	goOutputPath := "testdata/out/go"
	goPackage := "github.com/mjschwenne/grackle/testdata/out/go"
	Grackle(&protoFiles, &gooseOutput, &coqLogicalPath, &coqPhysicalPath, nil, &goOutputPath, &goPackage, grackleOutput)
	grackleOutput.Flush()
	golden.Assert(t, grackleBuffer.String(), "golden/complete.golden")
}
