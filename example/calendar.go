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
	for _, e := range c.events {
		enc = MarshalEvent(e, enc)
	}

	return enc
}

func UnmarshalCalendar(s []byte) (Calendar, []byte) {
	var enc = s
	var events []Event
	var eventsLen uint64
	var newEvent Event

	eventsLen, enc = marshal.ReadInt(enc)
	for _ = range eventsLen {
		newEvent, enc = UnmarshalEvent(enc)
		events = append(events, newEvent)
	}

	return Calendar{events: events}, enc
}
