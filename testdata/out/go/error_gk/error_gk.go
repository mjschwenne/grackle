package error_gk

import "github.com/tchajed/marshal"

type E uint32

const (
	EOk        E = 0
	EEndOfFile E = 1
	EUnknown   E = 2
)

func Marshal(enc []byte, e E) []byte {
	return marshal.WriteInt32(enc, uint32(e))
}

func Unmarshal(s []byte) (E, []byte) {
	e_raw, s := marshal.ReadInt32(s)
	return E(e_raw), s
}

var Name = map[uint32]string{
	0: "eOk",
	1: "eEndOfFile",
	2: "eUnknown",
}

var Value = map[string]uint32{
	"eOk":        0,
	"eEndOfFile": 1,
	"eUnknown":   2,
}

func (e E) String() string {
	return Name[uint32(e)]
}
