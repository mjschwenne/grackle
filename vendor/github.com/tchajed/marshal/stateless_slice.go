package marshal

func ReadSlice[T any](b []byte, count uint64, readOne func(b []byte) (T, []byte)) ([]T, []byte) {
	var b2 = b
	var xs = []T{}
	for i := uint64(0); i < count; i++ {
		xNew, bNew := readOne(b2)
		xs = append(xs, xNew)
		b2 = bNew
	}
	return xs, b2
}

func ReadSliceLenPrefix[T any](b []byte, readOne func(b []byte) (T, []byte)) ([]T, []byte) {
	count, b2 := ReadInt(b)
	return ReadSlice(b2, count, readOne)
}

func WriteSlice[T any](b []byte, xs []T, writeOne func(b []byte, x T) []byte) []byte {
	var b2 = b
	for _, x := range xs {
		b2 = writeOne(b2, x)
	}
	return b2
}

func WriteSliceLenPrefix[T any](b []byte, xs []T, writeOne func(b []byte, x T) []byte) []byte {
	b2 := WriteInt(b, uint64(len(xs)))
	b3 := WriteSlice(b2, xs, writeOne)
	return b3
}
