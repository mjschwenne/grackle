//--------------------------------------
// This file is autogenerated by grackle
// DO NOT MANUALLY EDIT THIS FILE
//--------------------------------------

package complete_gk

import (
	"github.com/tchajed/marshal"

	"github.com/mjschwenne/grackle/testdata/out/go/completeint_gk"
	"github.com/mjschwenne/grackle/testdata/out/go/completeslice_gk"
)

type S struct {
	Int     completeint_gk.S
	Slc     completeslice_gk.S
	Success bool
}

func Marshal(c S, prefix []byte) []byte {
	var enc = prefix

	enc = completeint_gk.Marshal(c.Int, enc)
	enc = completeslice_gk.Marshal(c.Slc, enc)
	enc = marshal.WriteBool(enc, c.Success)

	return enc
}

func Unmarshal(s []byte) (S, []byte) {
	var enc = s // Needed for goose compatibility
	var int completeint_gk.S
	var slc completeslice_gk.S
	var success bool

	int, enc = completeint_gk.Unmarshal(enc)
	slc, enc = completeslice_gk.Unmarshal(enc)
	success, enc = marshal.ReadBool(enc)

	return S{
		Int:     int,
		Slc:     slc,
		Success: success,
	}, enc
}
