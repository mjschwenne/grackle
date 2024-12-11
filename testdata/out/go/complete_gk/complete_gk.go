package complete_gk

import (
	"github.com/goose-lang/primitive"

	"github.com/tchajed/marshal"

	"github.com/mjschwenne/grackle/testdata/out/go/completeint_gk"
	"github.com/mjschwenne/grackle/testdata/out/go/completeslice_gk"
)

type S struct {
	Int     *completeint_gk.S
	Slc     *completeslice_gk.S
	Success bool
}

func (c *S) approxSize() uint64 {
	return 0
}

func Marshal(c *S, prefix []byte) []byte {
	var enc = prefix

	primitive.Assume(c.Int != nil)
	enc = completeint_gk.Marshal(c.Int, enc)
	primitive.Assume(c.Slc != nil)
	enc = completeslice_gk.Marshal(c.Slc, enc)
	enc = marshal.WriteBool(enc, c.Success)

	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	c := new(S)
	var enc = s // Needed for goose compatibility

	c.Int, enc = completeint_gk.Unmarshal(enc)
	c.Slc, enc = completeslice_gk.Unmarshal(enc)
	c.Success, enc = marshal.ReadBool(enc)

	return c, enc
}