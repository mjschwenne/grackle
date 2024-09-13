package main

import (
	"github.com/goose-lang/std"
	"github.com/tchajed/marshal"
)

type Event struct {
	id    uint32
	start *TimeStamp
	end   *TimeStamp
}

func (e *Event) approxSize() uint64 {
	size := std.SumAssumeNoOverflow(4, e.start.approxSize())
	return std.SumAssumeNoOverflow(size, e.end.approxSize())
}

func MarshalEvent(e *Event, prefix []byte) []byte {
	var enc = make([]byte, 0, e.approxSize())
	enc = marshal.WriteInt32(enc, e.id)
	enc = MarshalTimeStamp(e.start, enc)
	enc = MarshalTimeStamp(e.end, enc)
	return append(prefix, enc...)
}

func UnmarshalEvent(s []byte) (*Event, []byte) {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)
	e.start, enc = UnmarshalTimeStamp(enc)
	e.end, enc = UnmarshalTimeStamp(enc)
	return e, enc
}
