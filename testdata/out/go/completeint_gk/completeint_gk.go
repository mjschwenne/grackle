package completeint_gk

import (
	"github.com/tchajed/marshal"
)

type S struct {
	One   uint32
	Two   uint32
	Three uint32
	Four  uint64
	Five  uint64
	Six   uint64
}

func (c *S) approxSize() uint64 {
	return 0
}

func Marshal(c *S, prefix []byte) []byte {
	var enc = prefix

	enc = marshal.WriteInt32(enc, c.One)
	enc = marshal.WriteInt32(enc, c.Two)
	enc = marshal.WriteInt32(enc, c.Three)
	enc = marshal.WriteInt(enc, c.Four)
	enc = marshal.WriteInt(enc, c.Five)
	enc = marshal.WriteInt(enc, c.Six)

	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	c := new(S)
	var enc = s // Needed for goose compatibility

	c.One, enc = marshal.ReadInt32(enc)
	c.Two, enc = marshal.ReadInt32(enc)
	c.Three, enc = marshal.ReadInt32(enc)
	c.Four, enc = marshal.ReadInt(enc)
	c.Five, enc = marshal.ReadInt(enc)
	c.Six, enc = marshal.ReadInt(enc)

	return c, enc
}
