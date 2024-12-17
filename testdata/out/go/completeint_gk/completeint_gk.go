//--------------------------------------
// This file is autogenerated by grackle
// DO NOT MANUALLY EDIT THIS FILE
//--------------------------------------

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

func Marshal(c S, prefix []byte) []byte {
	var enc = prefix

	enc = marshal.WriteInt32(enc, c.One)
	enc = marshal.WriteInt32(enc, c.Two)
	enc = marshal.WriteInt32(enc, c.Three)
	enc = marshal.WriteInt(enc, c.Four)
	enc = marshal.WriteInt(enc, c.Five)
	enc = marshal.WriteInt(enc, c.Six)

	return enc
}

func Unmarshal(s []byte) (S, []byte) {
	var enc = s // Needed for goose compatibility
	var one uint32
	var two uint32
	var three uint32
	var four uint64
	var five uint64
	var six uint64

	one, enc = marshal.ReadInt32(enc)
	two, enc = marshal.ReadInt32(enc)
	three, enc = marshal.ReadInt32(enc)
	four, enc = marshal.ReadInt(enc)
	five, enc = marshal.ReadInt(enc)
	six, enc = marshal.ReadInt(enc)

	return S{
		One:   one,
		Two:   two,
		Three: three,
		Four:  four,
		Five:  five,
		Six:   six,
	}, enc
}
