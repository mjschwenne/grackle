package main

import (
	"github.com/tchajed/marshal"
)

type Status uint64

const (
	STATUS_UNSPECIFIED Status = 0
	STATUS_STUDENT     Status = 1
	STATUS_STAFF       Status = 2
	STATUS_PROFESSOR   Status = 2
)

type Person_Status struct {
	status Status
}

func (ps *Person_Status) SetStatus(s Status) {
	if s == STATUS_STUDENT {
		ps.status = s
	} else if s == STATUS_STAFF {
		ps.status = s
	} else if s == STATUS_PROFESSOR {
		ps.status = s
	} else {
		ps.status = STATUS_UNSPECIFIED
	}
}

func (ps *Person_Status) GetStatus() Status {
	return ps.status
}

func MarshalPersonStatus(enc []byte, ps Person_Status) []byte {
	enc = marshal.WriteInt(enc, uint64(ps.status))
	return enc
}

func UnmarshalPersonStatus(s []byte) (Person_Status, []byte) {
	status_int, s := marshal.ReadInt(s)
	status := Person_Status{}
	status.SetStatus(Status(status_int))
	return status, s
}

type Person struct {
	Name   string
	Status Person_Status
}

func MarshalPerson(enc []byte, p Person) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(p.Name))
	enc = MarshalPersonStatus(enc, p.Status)
	return enc
}

func UnmarshalPerson(s []byte) (Person, []byte) {
	name, s := marshal.ReadLenPrefixedBytes(s)
	status_int, s := marshal.ReadInt(s)
	status := Person_Status{}
	status.SetStatus(Status(status_int))

	return Person{
		Name:   string(name),
		Status: status,
	}, s
}
