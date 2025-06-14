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

func Marshal(enc []byte, c S) []byte {
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

	strgLen, s := marshal.ReadInt(s)
	strgBytes, s := marshal.ReadBytesCopy(s, strgLen)
	strg := string(strgBytes)
	strg2Len, s := marshal.ReadInt(s)
	strg2Bytes, s := marshal.ReadBytesCopy(s, strg2Len)
	strg2 := string(strg2Bytes)
	bytesLen, s := marshal.ReadInt(s)
	bytesBytes, s := marshal.ReadBytesCopy(s, bytesLen)
	bytes := bytesBytes
	bytes2Len, s := marshal.ReadInt(s)
	bytes2Bytes, s := marshal.ReadBytesCopy(s, bytes2Len)
	bytes2 := bytes2Bytes

	return S{
		Strg:   strg,
		Strg2:  strg2,
		Bytes:  bytes,
		Bytes2: bytes2,
	}, s
}
