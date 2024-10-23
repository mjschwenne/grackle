package event_gk

import (
	"github.com/mjschwenne/grackle/testdata/out/go/timestamp_gk"
	"github.com/tchajed/marshal"
)

type S struct {
	Id        uint32
	Name      *[]byte
	StartTime *timestamp_gk.S
	EndTime   *timestamp_gk.S
}

func (e *S) approxSize() uint64 {
	return 0
}

func Marshal(e *S, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, e.Id)
	enc = marshal.WriteInt(enc, uint64(len(*e.Name)))
	enc = marshal.WriteBytes(enc, *e.Name)
	enc = timestamp_gk.Marshal(e.StartTime, enc)
	enc = timestamp_gk.Marshal(e.EndTime, enc)
	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	e := new(S)
	var enc = s // Needed for goose compatibility

	e.Id, enc = marshal.ReadInt32(enc)
	var nameLen uint64
	var name []byte
	nameLen, enc = marshal.ReadInt(enc)
	name, enc = marshal.ReadBytesCopy(enc, nameLen)
	e.Name = &name
	e.StartTime, enc = timestamp_gk.Unmarshal(enc)
	e.EndTime, enc = timestamp_gk.Unmarshal(enc)
	return e, enc
}
