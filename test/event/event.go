package Event_gk

import (
	"github.com/mjschwenne/grackle/test/timestamp"
	"github.com/tchajed/marshal"
)

type Event struct {
	id        uint32
	startTime *TimeStamp_gk.TimeStamp
	endTime   *TimeStamp_gk.TimeStamp
}

func (e *Event) approxSize() uint64 {
	return 0
}

func MarshalEvent(e *Event, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, e.id)
	enc = TimeStamp_gk.MarshalTimeStamp(e.startTime, enc)
	enc = TimeStamp_gk.MarshalTimeStamp(e.endTime, enc)
	return enc
}

func UnmarshalEvent(s []byte) (*Event, []byte) {
	e := new(Event)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)
	e.startTime, enc = TimeStamp_gk.UnmarshalTimeStamp(enc)
	e.endTime, enc = TimeStamp_gk.UnmarshalTimeStamp(enc)
	return e, enc
}
