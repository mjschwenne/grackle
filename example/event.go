package main

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	id    uint32
	start *TimeStamp
	end   *TimeStamp
}

func (e *Event) maxSize() uint64 {
	return 4 + e.start.maxSize() + e.end.maxSize()
}

func MarshalEvent(e *Event, prefix []byte) []byte {
	// Getting the length right during code generation could be tricky
	// How important is knowing the capacity in the first place?
	var enc = make([]byte, 0, e.maxSize())
	enc = marshal.WriteInt32(enc, e.id)
	enc = MarshalTimeStamp(e.start, enc)
	enc = MarshalTimeStamp(e.end, enc)
	return append(prefix, enc...)
}

func UnmarshalEvent(s []byte) (*Event, []byte) {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)
	e.start, enc = UnmarshalTimeStamp(enc[:12])
	e.end, enc = UnmarshalTimeStamp(enc[:12])
	return e, enc
}
