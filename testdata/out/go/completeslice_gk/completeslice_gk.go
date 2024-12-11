package completeslice_gk

import (
	"github.com/tchajed/marshal"
)

type S struct {
	Strg string
	Byte []byte
}

func (c *S) approxSize() uint64 {
	return 0
}

func Marshal(c *S, prefix []byte) []byte {
	var enc = prefix

	strgBytes := []byte(c.Strg)
	enc = marshal.WriteInt(enc, uint64(len(strgBytes)))
	enc = marshal.WriteBytes(enc, strgBytes)
	enc = marshal.WriteInt(enc, uint64(len(c.Byte)))
	enc = marshal.WriteBytes(enc, c.Byte)

	return enc
}

func Unmarshal(s []byte) (*S, []byte) {
	c := new(S)
	var enc = s // Needed for goose compatibility

	var strgLen uint64
	var strgBytes []byte
	strgLen, enc = marshal.ReadInt(enc)
	strgBytes, enc = marshal.ReadBytesCopy(enc, strgLen)
	c.Strg = string(strgBytes)
	var byteLen uint64
	var byteBytes []byte
	byteLen, enc = marshal.ReadInt(enc)
	byteBytes, enc = marshal.ReadBytesCopy(enc, byteLen)
	c.Byte = byteBytes

	return c, enc
}