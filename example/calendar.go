package main

import (
	"github.com/tchajed/marshal"
)

type Calendar struct {
	events []Event
}

func MarshalCalendar(c Calendar, prefix []byte) []byte {
	var enc = prefix

	enc = marshal.WriteInt(enc, uint64(len(c.events)))
	enc = marshal.WriteSlice(prefix, c.events, MarshalEvent)

	return enc
}

func UnmarshalCalendar(s []byte) (Calendar, []byte) {
	var enc = s
	var events []Event
	var eventsLen uint64

	eventsLen, enc = marshal.ReadInt(enc)
	events, enc = marshal.ReadSlice(enc, eventsLen, UnmarshalEvent)

	return Calendar{events: events}, enc
}
