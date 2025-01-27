//--------------------------------------
// This file is autogenerated by grackle
// DO NOT MANUALLY EDIT THIS FILE
//--------------------------------------

package structslice_gk

import (
	"github.com/tchajed/marshal"

	"github.com/mjschwenne/grackle/testdata/out/go/completeint_gk"
	"github.com/mjschwenne/grackle/testdata/out/go/completeslice_gk"
)

type S struct {
	Slices []completeslice_gk.S
	Ints   []completeint_gk.S
}

func Marshal(prefix []byte, s S) []byte {
	var enc = prefix

	enc = marshal.WriteInt(enc, uint64(len(s.Slices)))
	enc = marshal.WriteSlice(enc, s.Slices, completeslice_gk.Marshal)

	enc = marshal.WriteInt(enc, uint64(len(s.Ints)))
	enc = marshal.WriteSlice(enc, s.Ints, completeint_gk.Marshal)

	return enc
}

func Unmarshal(s []byte) (S, []byte) {
	var enc = s // Needed for goose compatibility
	var slices []completeslice_gk.S
	var ints []completeint_gk.S

	var slicesLen uint64
	slicesLen, enc = marshal.ReadInt(enc)
	slices, enc = marshal.ReadSlice(enc, slicesLen, completeslice_gk.Unmarshal)
	var intsLen uint64
	intsLen, enc = marshal.ReadInt(enc)
	ints, enc = marshal.ReadSlice(enc, intsLen, completeint_gk.Unmarshal)

	return S{
		Slices: slices,
		Ints:   ints,
	}, enc
}
