package main

import "github.com/tchajed/marshal"

type Calendar struct {
	events []Event
}

func MarshalCalendar(enc []byte, c Calendar) []byte {
	enc = marshal.WriteInt(enc, uint64(len(c.events)))
	return marshal.WriteSlice[Event](enc, c.events, MarshalEvent)
}

func UnmarshalCalendar(s []byte) (Calendar, []byte) {
	eventsLen, s := marshal.ReadInt(s)
	events, s := marshal.ReadSlice[Event](s, eventsLen, UnmarshalEvent)

	return Calendar{
		events: events,
	}, s
}
