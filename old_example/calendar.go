package main

import (
	"github.com/tchajed/marshal"
)

type Calendar struct {
	events []Event
}

func MarshalCalendar(prefix []byte, c Calendar) []byte {
	var enc = prefix

	enc = marshal.WriteInt(enc, uint64(len(c.events)))
	enc = marshal.WriteSlice[Event](enc, c.events, MarshalEvent)

	return enc
}

func UnmarshalCalendar(s []byte) (Calendar, []byte) {
	var enc = s
	var events []Event
	var eventsLen uint64

	eventsLen, enc = marshal.ReadInt(enc)
	events, enc = marshal.ReadSlice[Event](enc, eventsLen, UnmarshalEvent)

	return Calendar{events: events}, enc
}
