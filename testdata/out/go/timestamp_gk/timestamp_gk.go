//--------------------------------------
// This file is autogenerated by grackle
// DO NOT MANUALLY EDIT THIS FILE
//--------------------------------------

package timestamp_gk

import (
	"github.com/tchajed/marshal"
)

type S struct {
	Hour   uint32
	Minute uint32
	Second uint64
}

func Marshal(prefix []byte, t S) []byte {
	var enc = prefix

	enc = marshal.WriteInt32(enc, t.Hour)
	enc = marshal.WriteInt32(enc, t.Minute)
	enc = marshal.WriteInt(enc, t.Second)

	return enc
}

func Unmarshal(s []byte) (S, []byte) {
	var enc = s // Needed for goose compatibility
	var hour uint32
	var minute uint32
	var second uint64

	hour, enc = marshal.ReadInt32(enc)
	minute, enc = marshal.ReadInt32(enc)
	second, enc = marshal.ReadInt(enc)

	return S{
		Hour:   hour,
		Minute: minute,
		Second: second,
	}, enc
}
