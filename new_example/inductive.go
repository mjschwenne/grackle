package main

import "github.com/tchajed/marshal"

type Corpus uint64

// BEGIN : Const block style enum

const (
	CORPUS_UNSPECIFIED = iota
	CORPUS_WEB
	CORPUS_NEWS
)

type eQuery struct {
	query  string
	corpus Corpus
}

func MarshalEQuery(enc []byte, q eQuery) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.query))
	enc = marshal.WriteInt(enc, uint64(q.corpus))
	return enc
}

func UnmarshalEQuery(s []byte) (eQuery, []byte) {
	query, s := marshal.ReadLenPrefixedBytes(s)
	corpus, s := marshal.ReadInt(s)

	return eQuery{
		query:  string(query),
		corpus: Corpus(corpus),
	}, s
}

// BEGIN : Bool protected inductive enum

type Address struct {
	line1 string
	line2 string
	city  string
	state string
	zip   uint32
}

func MarshalAddress(enc []byte, a Address) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(a.line1))
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(a.line2))
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(a.city))
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(a.state))
	enc = marshal.WriteInt32(enc, a.zip)
	return enc
}

func UnmarshalAddress(s []byte) (Address, []byte) {
	line1, s := marshal.ReadLenPrefixedBytes(s)
	line2, s := marshal.ReadLenPrefixedBytes(s)
	city, s := marshal.ReadLenPrefixedBytes(s)
	state, s := marshal.ReadLenPrefixedBytes(s)
	zip, s := marshal.ReadInt32(s)

	return Address{
		line1: string(line1),
		line2: string(line2),
		city:  string(city),
		state: string(state),
		zip:   zip,
	}, s
}

type bQuery struct {
	query    string
	has_URL  bool
	URL      string
	has_addr bool
	addr     Address
}

func MarshalBQuery(enc []byte, q bQuery) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.query))
	if q.has_addr {
		enc = marshal.WriteInt32(enc, 2)
		enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.URL))
	} else if q.has_URL {
		enc = marshal.WriteInt32(enc, 3)
		enc = MarshalAddress(enc, q.addr)
	}
	return enc
}

func UnmarshalBQuery(s []byte) (bQuery, []byte) {
	query, s := marshal.ReadLenPrefixedBytes(s)
	selector, s := marshal.ReadInt32(s)

	var has_URL bool
	var URL []byte
	var has_addr bool
	var addr Address
	if selector == 2 {
		has_URL = true
		URL, s = marshal.ReadLenPrefixedBytes(s)
	} else if selector == 3 {
		has_addr = true
		addr, s = UnmarshalAddress(s)
	} else {
		panic("Unknown selector value!")
	}

	return bQuery{
		query:    string(query),
		has_URL:  has_URL,
		URL:      string(URL),
		has_addr: has_addr,
		addr:     addr,
	}, s
}

// BEGIN : Interface inductive enum

type iCorpus interface {
	isCorpus() bool
}

type URL struct {
	contents string
}

func (u URL) isCorpus() bool {
	return true
}

type Addr struct {
	contents Address
}

func (a Addr) isCorpus() bool {
	return true
}

type iQuery struct {
	query  string
	corpus iCorpus
}

func MarshalIQuery(enc []byte, q iQuery) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.query))
	switch c := q.corpus.(type) {
	case URL:
		enc = marshal.WriteInt32(enc, 2)
		enc = marshal.WriteLenPrefixedBytes(enc, []byte(c.contents))
	case Addr:
		enc = marshal.WriteInt32(enc, 3)
		enc = MarshalAddress(enc, c.contents)
	default:
		panic("Unexpected iCorpus type")
	}
	return enc
}

func UnmarshalIQuery(s []byte) (iQuery, []byte) {
	query, s := marshal.ReadLenPrefixedBytes(s)
	selector, s := marshal.ReadInt32(s)

	var corpus iCorpus
	switch selector {
	case 2:
		var contents []byte
		contents, s = marshal.ReadLenPrefixedBytes(s)
		corpus = URL{
			contents: string(contents),
		}
	case 3:
		var contents Address
		contents, s = UnmarshalAddress(s)
		corpus = Addr{
			contents: contents,
		}
	}

	return iQuery{
		query:  string(query),
		corpus: corpus,
	}, s
}
