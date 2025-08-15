package example

import "github.com/tchajed/marshal"

type TimeStamp struct {
	hour   uint32
	minute uint32
	second uint32
}

func MarshalTimeStamp(enc []byte, t TimeStamp) []byte {
	enc = marshal.WriteInt32(enc, t.hour)
	enc = marshal.WriteInt32(enc, t.minute)
	enc = marshal.WriteInt32(enc, t.second)
	return enc
}

func UnmarshalTimeStamp(s []byte) (TimeStamp, []byte) {
	hour, s := marshal.ReadInt32(s)
	minute, s := marshal.ReadInt32(s)
	second, s := marshal.ReadInt32(s)

	return TimeStamp{
		hour:   hour,
		minute: minute,
		second: second,
	}, s
}
