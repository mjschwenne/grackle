package example

import "github.com/tchajed/marshal"
import "github.com/goose-lang/std"

type Calendar struct {
	hash   []byte
	events []Event
}

func MarshalCalendar(enc []byte, c Calendar) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, c.hash)
	enc = marshal.WriteInt(enc, uint64(len(c.events)))
	return marshal.WriteSlice[Event](enc, c.events, MarshalEvent)
}

func UnmarshalCalendar(s []byte) (Calendar, []byte) {
	hash, s := marshal.ReadLenPrefixedBytes(s)
	hash = std.BytesClone(hash)
	eventsLen, s := marshal.ReadInt(s)
	events, s := marshal.ReadSlice[Event](s, eventsLen, UnmarshalEvent)

	return Calendar{
		hash:   hash,
		events: events,
	}, s
}
