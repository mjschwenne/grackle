package main

import (
	"github.com/tchajed/marshal"
)

type TimeStamp struct {
	hour   uint32
	minute uint32
	second uint32
}

func MarshalTimeStamp(t *TimeStamp) []byte {
	var enc = make([]byte, 0, 12)
	enc = marshal.WriteInt32(enc, t.hour)
	enc = marshal.WriteInt32(enc, t.minute)
	enc = marshal.WriteInt32(enc, t.second)
	return enc
}

func UnmarshalTimeStamp(s []byte) *TimeStamp {
	t := new(TimeStamp)
	var enc = s // Needed for goose compatibility
	t.hour, enc = marshal.ReadInt32(enc)
	t.minute, enc = marshal.ReadInt32(enc)
	t.second, enc = marshal.ReadInt32(enc)
	return t
}
