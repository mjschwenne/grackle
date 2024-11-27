package completewithbool_gk

import (
	"github.com/goose-lang/primitive"

	"github.com/tchajed/marshal"

	"github.com/mjschwenne/grackle/testdata/out/go/completemessage_gk"
)

type S struct {
	Msg     *completemessage_gk.S
	Success bool
}

func (c *S) approxSize() uint64 {
	return 0
}

func Marshal(c *S, prefix []byte) []byte {
	var enc = prefix

	primitive.Assume(c.Msg != nil)
	enc = completemessage_gk.Marshal(c.Msg, enc)
	enc = marshal.WriteBool(enc, c.Success)

	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	c := new(S)
	var enc = s // Needed for goose compatibility

	c.Msg, enc = completemessage_gk.Unmarshal(enc)
	c.Success, enc = marshal.ReadBool(enc)

	return c, enc
}
