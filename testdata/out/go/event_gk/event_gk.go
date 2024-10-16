package event_gk

import (
	"github.com/mjschwenne/grackle/testdata/out/go/timestamp_gk"
	"github.com/tchajed/marshal"
)

type S struct {
	id        uint32
	startTime *timestamp_gk.S
	endTime   *timestamp_gk.S
}

func (e *S) approxSize() uint64 {
	return 0
}

func Marshal(e *S, prefix []byte) []byte {
	var enc = prefix
	enc = marshal.WriteInt32(enc, e.id)
	enc = timestamp_gk.Marshal(e.startTime, enc)
	enc = timestamp_gk.Marshal(e.endTime, enc)
	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	e := new(S)
	var enc = s // Needed for goose compatibility
	e.id, enc = marshal.ReadInt32(enc)
	e.startTime, enc = timestamp_gk.Unmarshal(enc)
	e.endTime, enc = timestamp_gk.Unmarshal(enc)
	return e, enc
}
