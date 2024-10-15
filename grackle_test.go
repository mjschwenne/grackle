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
	if actual != "example/Event_proof.v" {
		t.Errorf("Wanted `example/Event_proof.v`, got %v\n", actual)
	}
}

func TestCalendarExample(t *testing.T) {
	grackleBuffer := bytes.NewBuffer(make([]byte, 0, 10000))
	grackleOutput := bufio.NewWriter(grackleBuffer)
	protoFiles := "testdata/proto"
	gooseOutput := "example"
	coqLogicalPath := "Grackle.example"
	coqPhysicalPath := "example"
	goOutputPath := "example"
	goPackage := "github.com/mjschwenne/grackle/example"
	Grackle(&protoFiles, &gooseOutput, &coqLogicalPath, &coqPhysicalPath, &goOutputPath, &goPackage, grackleOutput)
	grackleOutput.Flush()
	golden.Assert(t, grackleBuffer.String(), "golden/calendar.golden")
}
