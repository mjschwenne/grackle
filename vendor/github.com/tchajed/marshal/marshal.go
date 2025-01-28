package marshal

import (
	"github.com/goose-lang/primitive"
)

// Enc is a stateful encoder for a statically-allocated array.
type Enc struct {
	b   []byte
	off *uint64
}

func NewEncFromSlice(b []byte) Enc {
	return Enc{
		b:   b,
		off: new(uint64),
	}
}

func NewEnc(sz uint64) Enc {
	b := make([]byte, sz)
	return NewEncFromSlice(b)
}

func (enc Enc) PutInt(x uint64) {
	off := *enc.off
	primitive.UInt64Put(enc.b[off:], x)
	*enc.off += 8
}

func (enc Enc) PutInt32(x uint32) {
	off := *enc.off
	primitive.UInt32Put(enc.b[off:], x)
	*enc.off += 4
}

func (enc Enc) PutInts(xs []uint64) {
	for _, x := range xs {
		enc.PutInt(x)
	}
}

func (enc Enc) PutBytes(b []byte) {
	off := *enc.off
	n := uint64(copy(enc.b[off:], b))
	*enc.off += n // should be len(b) (unless too much data was provided)
}

func bool2byte(b bool) byte {
	if b {
		return 1
	} else {
		return 0
	}
}

func (enc Enc) PutBool(b bool) {
	off := *enc.off
	enc.b[off] = bool2byte(b)
	*enc.off += 1
}

func (enc Enc) Finish() []byte {
	return enc.b
}

// Dec is a stateful decoder that returns values encoded
// sequentially in a single slice.
type Dec struct {
	b   []byte
	off *uint64
}

func NewDec(b []byte) Dec {
	return Dec{b: b, off: new(uint64)}
}

func (dec Dec) GetInt() uint64 {
	off := *dec.off
	*dec.off += 8
	return primitive.UInt64Get(dec.b[off:])
}

func (dec Dec) GetInt32() uint32 {
	off := *dec.off
	*dec.off += 4
	return primitive.UInt32Get(dec.b[off:])
}

func (dec Dec) GetInts(num uint64) []uint64 {
	var xs []uint64
	for i := uint64(0); i < num; i++ {
		xs = append(xs, dec.GetInt())
	}
	return xs
}

func (dec Dec) GetBytes(num uint64) []byte {
	off := *dec.off
	b := dec.b[off : off+num]
	*dec.off += num
	return b
}

func (dec Dec) GetBool() bool {
	off := *dec.off
	*dec.off += 1
	if dec.b[off] == 0 {
		return false
	} else {
		return true
	}
}
