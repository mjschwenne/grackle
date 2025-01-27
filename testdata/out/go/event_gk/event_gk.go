//--------------------------------------
// This file is autogenerated by grackle
// DO NOT MANUALLY EDIT THIS FILE
//--------------------------------------

package event_gk

import (
	"github.com/tchajed/marshal"

	"github.com/mjschwenne/grackle/testdata/out/go/timestamp_gk"
)

type S struct {
	Id        uint32
	Name      string
	StartTime timestamp_gk.S
	EndTime   timestamp_gk.S
}

func Marshal(prefix []byte, e S) []byte {
	var enc = prefix

	enc = marshal.WriteInt32(enc, e.Id)
	nameBytes := []byte(e.Name)
	enc = marshal.WriteInt(enc, uint64(len(nameBytes)))
	enc = marshal.WriteBytes(enc, nameBytes)
	enc = timestamp_gk.Marshal(enc, e.StartTime)
	enc = timestamp_gk.Marshal(enc, e.EndTime)

	return enc
}

func Unmarshal(s []byte) (S, []byte) {
	var enc = s // Needed for goose compatibility
	var id uint32
	var name string
	var startTime timestamp_gk.S
	var endTime timestamp_gk.S

	id, enc = marshal.ReadInt32(enc)
	var nameLen uint64
	var nameBytes []byte
	nameLen, enc = marshal.ReadInt(enc)
	nameBytes, enc = marshal.ReadBytesCopy(enc, nameLen)
	name = string(nameBytes)
	startTime, enc = timestamp_gk.Unmarshal(enc)
	endTime, enc = timestamp_gk.Unmarshal(enc)

	return S{
		Id:        id,
		Name:      name,
		StartTime: startTime,
		EndTime:   endTime,
	}, enc
}
