package main

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	id        uint32
	name      string
	startTime TimeStamp
	endTime   TimeStamp
}

func MarshalEvent(enc []byte, e Event) []byte {
	enc = marshal.WriteInt32(enc, e.id)
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(e.name))
	enc = MarshalTimeStamp(enc, e.startTime)
	enc = MarshalTimeStamp(enc, e.endTime)
	return enc
}

func UnmarshalEvent(s []byte) (Event, []byte) {
	id, s := marshal.ReadInt32(s)
	nameBytes, s := marshal.ReadLenPrefixedBytes(s)

	startTime, s := UnmarshalTimeStamp(s)
	endTime, s := UnmarshalTimeStamp(s)
	return Event{
		id:        id,
		name:      string(nameBytes),
		startTime: startTime,
		endTime:   endTime,
	}, s
}
