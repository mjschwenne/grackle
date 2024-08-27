package main

import (
	"github.com/goose-lang/primitive"
)

type TimeStamp struct {
	hour   uint32
	minute uint32
	second uint32
}

func (t TimeStamp) marshal() []byte {
	enc := make([]byte, 12)
	var off uint32 = 0
	primitive.UInt32Put(enc[off:], t.hour)
	off += 4
	primitive.UInt32Put(enc[off:], t.minute)
	off += 4
	primitive.UInt32Put(enc[off:], t.second)

	return enc
}

func UnmarshalTimeStamp(enc []byte) *TimeStamp {
	// var err error = nil
	var ts TimeStamp
	// if len(enc) != 12 {
	// 	err = errors.New(fmt.Sprintf("encoding has incorrect number of bytes (%v), 12 expected.", len(enc)))
	// 	return nil, err
	// }

	var off uint32
	ts.hour = primitive.UInt32Get(enc[off:])
	off += 4
	ts.minute = primitive.UInt32Get(enc[off:])
	off += 4
	ts.second = primitive.UInt32Get(enc[off:])

	return &ts //, err
}
