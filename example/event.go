package main

import (
	"github.com/tchajed/marshal"
)

type Event struct {
	id        uint32
	name      string
	startTime TimeStamp
	endTime   TimeStamp
}

func MarshalEvent(prefix []byte, e Event) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, e.id)

	nameByte := []byte(e.name)
	enc = marshal.WriteInt(enc, uint64(len(nameByte)))
	enc = marshal.WriteBytes(enc, nameByte)

	enc = MarshalTimeStamp(enc, e.startTime)
	enc = MarshalTimeStamp(enc, e.endTime)
	return enc
}

func UnmarshalEvent(s []byte) (Event, []byte) {
	var enc = s // Needed for goose compatibility
	var id uint32
	var name string
	var startTime TimeStamp
	var endTime TimeStamp

	id, enc = marshal.ReadInt32(enc)

	var nameLen uint64
	var nameBytes []byte
	nameLen, enc = marshal.ReadInt(enc)
	nameBytes, enc = marshal.ReadBytesCopy(enc, nameLen)
	name = string(nameBytes)

	startTime, enc = UnmarshalTimeStamp(enc)
	endTime, enc = UnmarshalTimeStamp(enc)
	return Event{
		id:        id,
		name:      name,
		startTime: startTime,
		endTime:   endTime,
	}, enc
}
