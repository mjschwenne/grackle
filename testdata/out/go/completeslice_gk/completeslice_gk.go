//--------------------------------------
// This file is autogenerated by grackle
// DO NOT MANUALLY EDIT THIS FILE
//--------------------------------------

package completeslice_gk

import (
	"github.com/tchajed/marshal"
)

type S struct {
	Strg   string
	Strg2  string
	Bytes  []byte
	Bytes2 []byte
}

func Marshal(prefix []byte, c S) []byte {
	var enc = prefix

	strgBytes := []byte(c.Strg)
	enc = marshal.WriteInt(enc, uint64(len(strgBytes)))
	enc = marshal.WriteBytes(enc, strgBytes)
	strg2Bytes := []byte(c.Strg2)
	enc = marshal.WriteInt(enc, uint64(len(strg2Bytes)))
	enc = marshal.WriteBytes(enc, strg2Bytes)
	enc = marshal.WriteInt(enc, uint64(len(c.Bytes)))
	enc = marshal.WriteBytes(enc, c.Bytes)
	enc = marshal.WriteInt(enc, uint64(len(c.Bytes2)))
	enc = marshal.WriteBytes(enc, c.Bytes2)

	return enc
}

func Unmarshal(s []byte) (S, []byte) {
	var enc = s // Needed for goose compatibility
	var strg string
	var strg2 string
	var bytes []byte
	var bytes2 []byte

	var strgLen uint64
	var strgBytes []byte
	strgLen, enc = marshal.ReadInt(enc)
	strgBytes, enc = marshal.ReadBytesCopy(enc, strgLen)
	strg = string(strgBytes)
	var strg2Len uint64
	var strg2Bytes []byte
	strg2Len, enc = marshal.ReadInt(enc)
	strg2Bytes, enc = marshal.ReadBytesCopy(enc, strg2Len)
	strg2 = string(strg2Bytes)
	var bytesLen uint64
	var bytesBytes []byte
	bytesLen, enc = marshal.ReadInt(enc)
	bytesBytes, enc = marshal.ReadBytesCopy(enc, bytesLen)
	bytes = bytesBytes
	var bytes2Len uint64
	var bytes2Bytes []byte
	bytes2Len, enc = marshal.ReadInt(enc)
	bytes2Bytes, enc = marshal.ReadBytesCopy(enc, bytes2Len)
	bytes2 = bytes2Bytes

	return S{
		Strg:   strg,
		Strg2:  strg2,
		Bytes:  bytes,
		Bytes2: bytes2,
	}, enc
}
