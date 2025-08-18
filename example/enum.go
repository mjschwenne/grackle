package example

import (
	"github.com/goose-lang/primitive"
	"github.com/tchajed/marshal"
)

type Status uint64

const (
	STATUS_UNSPECIFIED Status = 0
	STATUS_STUDENT     Status = 1
	STATUS_STAFF       Status = 2
	STATUS_PROFESSOR   Status = 3
)

// Wrapper for type aliasing compliance
func MarshalStatus(enc []byte, s Status) []byte {
	return marshal.WriteInt(enc, uint64(s))
}

func UnmarshalStatus(s []byte) (Status, []byte) {
	status_raw, s := marshal.ReadInt(s)
	return Status(status_raw), s
}

type Person struct {
	Name     string
	Status   Status
	Statuses []Status // Does this make sense? No, but I need to test repeated enums...
}

func MarshalPerson(enc []byte, p Person) []byte {
	primitive.AssumeNoStringOverflow(p.Name)
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(p.Name))
	enc = marshal.WriteInt(enc, uint64(p.Status))

	enc = marshal.WriteInt(enc, uint64(len(p.Statuses)))
	enc = marshal.WriteSlice[Status](enc, p.Statuses, MarshalStatus)
	return enc
}

func UnmarshalPerson(s []byte) (Person, []byte) {
	name, s := marshal.ReadLenPrefixedBytes(s)
	status_int, s := marshal.ReadInt(s)
	status := Status(status_int)
	statuses_len, s := marshal.ReadInt(s)
	statuses, s := marshal.ReadSlice[Status](s, statuses_len, UnmarshalStatus)

	return Person{
		Name:     string(name),
		Status:   status,
		Statuses: statuses,
	}, s
}
