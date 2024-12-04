package error

type E uint32

const (
	eOk        E = 0
	eEndOfFile E = 1
	eUnknown   E = 2
)

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

func (e E) Enum() *E {
	n := new(E)
	*n = e
	return n
}

func (e E) String() string {
	return Name[uint32(e)]
}
