package main

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

type Person struct {
	Name   string
	Status Status
}

func MarshalPerson(enc []byte, p Person) []byte {
	primitive.AssumeNoStringOverflow(p.Name)
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(p.Name))
	enc = marshal.WriteInt(enc, uint64(p.Status))
	return enc
}

func UnmarshalPerson(s []byte) (Person, []byte) {
	name, s := marshal.ReadLenPrefixedBytes(s)
	status_int, s := marshal.ReadInt(s)
	status := Status(status_int)

	return Person{
		Name:   string(name),
		Status: status,
	}, s
}
