package main

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	name  string
	start TimeStamp
	end   TimeStamp
}

func MarshalEvent(e *Event) []byte {
	// Getting the length right during code generation could be tricky
	// How important is knowing the capacity in the first place?
	var enc = make([]byte, 0, len(e.name)+24)
	enc = marshal.WriteBytes(enc, []byte(e.name))
	enc = marshal.WriteBytes(enc, MarshalTimeStamp(&e.start))
	enc = marshal.WriteBytes(enc, MarshalTimeStamp(&e.end))
	return enc
}

func UnmarshalEvent(s []byte) *Event {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	var str_l uint64 = uint64(len(s) - 24)
	var bytes []byte
	bytes, enc = marshal.ReadBytes(enc, str_l)
	e.name = string(bytes)
	e.start = *UnmarshalTimeStamp(enc[:12])
	enc = enc[12:]
	e.end = *UnmarshalTimeStamp(enc[:12])
	return e
}
