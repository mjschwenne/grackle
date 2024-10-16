package timestamp_gk

import (
	"github.com/tchajed/marshal"
)

type S struct {
	hour   uint32
	minute uint32
	second uint32
}

func (t *S) approxSize() uint64 {
	return 0
}

func Marshal(t *S, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, t.hour)
	enc = marshal.WriteInt32(enc, t.minute)
	enc = marshal.WriteInt32(enc, t.second)
	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	t := new(S)
	var enc = s // Needed for goose compatibility
	t.hour, enc = marshal.ReadInt32(enc)
	t.minute, enc = marshal.ReadInt32(enc)
	t.second, enc = marshal.ReadInt32(enc)
	return t, enc
}
