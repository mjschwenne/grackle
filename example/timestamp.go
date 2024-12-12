package main

import (
	"github.com/tchajed/marshal"
)

type TimeStamp struct {
	hour   uint32
	minute uint32
	second uint32
}

func MarshalTimeStamp(t TimeStamp, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, t.hour)
	enc = marshal.WriteInt32(enc, t.minute)
	enc = marshal.WriteInt32(enc, t.second)
	return enc
}

func UnmarshalTimeStamp(s []byte) (TimeStamp, []byte) {
	var enc = s // Needed for goose compatibility
	var hour uint32
	var minute uint32
	var second uint32

	hour, enc = marshal.ReadInt32(enc)
	minute, enc = marshal.ReadInt32(enc)
	second, enc = marshal.ReadInt32(enc)
	return TimeStamp{
		hour:   hour,
		minute: minute,
		second: second,
	}, enc
}
