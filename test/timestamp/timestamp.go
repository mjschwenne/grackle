package TimeStamp_gk

import (
	"github.com/tchajed/marshal"
)

type TimeStamp struct {
	hour   uint32
	minute uint32
	second uint32
}

func (t *TimeStamp) approxSize() uint64 {
	return 0
}

func MarshalTimeStamp(t *TimeStamp, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, t.hour)
	enc = marshal.WriteInt32(enc, t.minute)
	enc = marshal.WriteInt32(enc, t.second)
	return enc
}

func UnmarshalTimeStamp(s []byte) (*TimeStamp, []byte) {
	t := new(TimeStamp)
	var enc = s // Needed for goose compatibility
	t.hour, enc = marshal.ReadInt32(enc)
	t.minute, enc = marshal.ReadInt32(enc)
	t.second, enc = marshal.ReadInt32(enc)
	return t, enc
}
