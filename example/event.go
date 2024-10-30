package main

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	id        uint32
	name      string
	startTime *TimeStamp
	endTime   *TimeStamp
}

func (e *Event) approxSize() uint64 {
	return 0
}

func MarshalEvent(e *Event, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, e.id)

	nameByte := []byte(e.name)
	enc = marshal.WriteInt(enc, uint64(len(nameByte)))
	enc = marshal.WriteBytes(enc, nameByte)

	enc = MarshalTimeStamp(e.startTime, enc)
	enc = MarshalTimeStamp(e.endTime, enc)
	return enc
}

func UnmarshalEvent(s []byte) (*Event, []byte) {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)

	var nameLen uint64
	var nameBytes []byte
	nameLen, enc = marshal.ReadInt(enc)
	nameBytes, enc = marshal.ReadBytesCopy(enc, nameLen)
	e.name = string(nameBytes)

	e.startTime, enc = UnmarshalTimeStamp(enc)
	e.endTime, enc = UnmarshalTimeStamp(enc)
	return e, enc
}
