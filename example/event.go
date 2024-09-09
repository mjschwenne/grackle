package main

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	id    uint32
	start TimeStamp
	end   TimeStamp
}

func MarshalEvent(e *Event) []byte {
	// Getting the length right during code generation could be tricky
	// How important is knowing the capacity in the first place?
	var enc = make([]byte, 0, 28)
	enc = marshal.WriteInt32(enc, e.id)
	enc = marshal.WriteBytes(enc, MarshalTimeStamp(&e.start))
	enc = marshal.WriteBytes(enc, MarshalTimeStamp(&e.end))
	return enc
}

func UnmarshalEvent(s []byte) *Event {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)
	e.start = *UnmarshalTimeStamp(enc[:12])
	enc = enc[12:]
	e.end = *UnmarshalTimeStamp(enc[:12])
	return e
}
