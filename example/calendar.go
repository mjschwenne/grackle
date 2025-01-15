package main

import (
	"github.com/tchajed/marshal"
)

type Calendar struct {
	events []Event
}

func MarshalCalendar(c Calendar, prefix []byte) []byte {
	var enc = prefix

	enc = marshal.WriteSliceLenPrefix(prefix, c.events, MarshalEvent)

	return enc
}

func UnmarshalCalendar(s []byte) (Calendar, []byte) {
	var enc = s
	var events []Event

	events, enc = marshal.ReadSliceLenPrefix(enc, UnmarshalEvent)

	return Calendar{events: events}, enc
}
