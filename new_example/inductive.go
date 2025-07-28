//go:build !goose

package main

import (
	"github.com/tchajed/marshal"
)

type Corpus uint64

// BEGIN : Const block style enum

const (
	CORPUS_UNSPECIFIED Corpus = 0
	CORPUS_WEB         Corpus = 1
	CORPUS_NEWS        Corpus = 2
)

type eCorpus struct {
	corpus Corpus
}

func (e *eCorpus) SetCorpus(c Corpus) {
	if c == CORPUS_WEB {
		e.corpus = c
	} else if c == CORPUS_NEWS {
		e.corpus = c
	} else {
		e.corpus = c
	}
}

func (e *eCorpus) GetCorpus() Corpus {
	return e.corpus
}

type eQuery struct {
	query  string
	corpus eCorpus
}

func MarshalEQuery(enc []byte, q eQuery) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.query))
	enc = marshal.WriteInt(enc, uint64(q.corpus.GetCorpus()))
	return enc
}

func UnmarshalEQuery(s []byte) (eQuery, []byte) {
	query, s := marshal.ReadLenPrefixedBytes(s)
	corpus_int, s := marshal.ReadInt(s)
	corpus := eCorpus{}
	corpus.SetCorpus(Corpus(corpus_int))

	return eQuery{
		query:  string(query),
		corpus: corpus,
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
	query          string
	corpusSelector Corpus
	corpusURL      string
	corpusAddr     Address
}

func (q *bQuery) GetCorpusType() Corpus {
	return q.corpusSelector
}

// There should also be a method like this:
// func (q *bQuery) GetCorpus() < ... >
// But without using interfaces, there is no
// return type which makes sense.
//
// The interface method is also what protobuf itself uses

func (q *bQuery) GetURL() string {
	if q.corpusSelector == CORPUS_WEB {
		return q.corpusURL
	}
	return ""
}

func (q *bQuery) GetAddr() *Address {
	if q.corpusSelector == CORPUS_NEWS {
		return &q.corpusAddr
	}
	return nil
}

// While protobuf doesn't give a setter method,
// we need it since the fields are private in
// order to keep the selector up to date.

func (q *bQuery) SetAddr(addr *Address) {
	q.corpusSelector = CORPUS_NEWS
	q.corpusAddr = *addr
}

func (q *bQuery) SetURL(url string) {
	q.corpusSelector = CORPUS_WEB
	q.corpusURL = url
}

func MarshalBQuery(enc []byte, q bQuery) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.query))
	switch q.corpusSelector {
	case CORPUS_WEB:
		enc = marshal.WriteInt32(enc, 2)
		enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.corpusURL))
	case CORPUS_NEWS:
		enc = marshal.WriteInt32(enc, 3)
		enc = MarshalAddress(enc, q.corpusAddr)
	}
	return enc
}

func UnmarshalBQuery(s []byte) (bQuery, []byte) {
	query, s := marshal.ReadLenPrefixedBytes(s)
	selector, s := marshal.ReadInt32(s)

	var URL []byte
	var corp Corpus
	var addr Address
	if selector == 2 {
		corp = CORPUS_WEB
		URL, s = marshal.ReadLenPrefixedBytes(s)
	} else if selector == 3 {
		corp = CORPUS_NEWS
		addr, s = UnmarshalAddress(s)
	} else {
		corp = CORPUS_UNSPECIFIED
	}

	return bQuery{
		query:          string(query),
		corpusSelector: corp,
		corpusURL:      string(URL),
		corpusAddr:     addr,
	}, s
}

// BEGIN : Interface inductive enum

type iCorpus interface {
	isCorpus()
}

type URL struct {
	contents string
}

func (u URL) isCorpus() {}

type Addr struct {
	contents Address
}

func (a Addr) isCorpus() {}

type iQuery struct {
	Query  string
	Corpus iCorpus
}

func (q *iQuery) GetQuery() string {
	if q != nil {
		return q.Query
	}
	return ""
}

func (q *iQuery) GetCorpus() iCorpus {
	if q != nil {
		return q.Corpus
	}
	return nil
}

func (q *iQuery) GetURL() string {
	if q != nil {
		if q, ok := q.Corpus.(*URL); ok {
			return q.contents
		}
	}
	return ""
}

func (q *iQuery) GetAddr() *Address {
	if q != nil {
		if q, ok := q.Corpus.(*Addr); ok {
			return &q.contents
		}
	}
	return nil
}

// Interestingly, a setter method is not given by protobuf itself.
// You would need to manually insert the Address into an Addr and
// set it yourself.

func MarshalIQuery(enc []byte, q iQuery) []byte {
	enc = marshal.WriteLenPrefixedBytes(enc, []byte(q.Query))
	switch c := q.Corpus.(type) {
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
		Query:  string(query),
		Corpus: corpus,
	}, s
}

// My current take is actually to opposite of what I was thinking during my
// last meeting with Tej. The interface based method seems more promising
// since it allows for direct access to the oneof field without requiring a
// pattern like this:
//
// switch msg.GetCorpusSelector() {
// case CORPUS_WEB:
//      ...
//      msg.GetURL()
//      ...
// case CORPUS_NEW:
//      ...
//      msg.GetAddr()
//      ...
// default:
//      ...
//      handle CORPUS_UNSPECIFIED case
//      ...
// }
//
// Although even if you got an iCorpus back, you would probably need to
// type cast it with either a type switch
//
// switch c := msg.GetCorpus().(type) {
// case URL:
//      ...
// case Addr:
//      ...
// }
//
// or a cast (if c, ok := msg.Corpus.(URL); ok), but if you're only interested
// in one, just use the getter method above.
//
// I also think that the interface based method will mirror the constructed Coq types
// more closely, which may ease the proof burden. Although it will require goose support
// for type switches and type casts.
