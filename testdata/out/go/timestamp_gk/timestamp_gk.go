package timestamp_gk

import (
	"github.com/tchajed/marshal"
)

type S struct {
	Hour   uint32
	Minute uint32
	Second uint64
}

func (t *S) approxSize() uint64 {
	return 0
}

func Marshal(t *S, prefix []byte) []byte {
	var enc = prefix

	enc = marshal.WriteInt32(enc, t.Hour)
	enc = marshal.WriteInt32(enc, t.Minute)
	enc = marshal.WriteInt(enc, t.Second)

	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	t := new(S)
	var enc = s // Needed for goose compatibility

	t.Hour, enc = marshal.ReadInt32(enc)
	t.Minute, enc = marshal.ReadInt32(enc)
	t.Second, enc = marshal.ReadInt(enc)

	return t, enc
}
