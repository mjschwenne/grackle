package test

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	id        uint32
	startTime *TimeStamp
	endTime   *TimeStamp
}

func (e *Event) approxSize() uint64 {
	return 0
}

func MarshalEvent(e *Event, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, e.id)
	enc = MarshalTimeStamp(e.startTime, enc)
	enc = MarshalTimeStamp(e.endTime, enc)
	return enc
}

func UnmarshalEvent(s []byte) (*Event, []byte) {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)
	e.startTime, enc = UnmarshalTimeStamp(enc)
	e.endTime, enc = UnmarshalTimeStamp(enc)
	return e, enc
}
