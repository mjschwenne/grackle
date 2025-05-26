package main

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

// BEGIN : Bool protected inductive enum

type address struct {
	line1 string
	line2 string
	city  string
	state string
	zip   uint32
}

type bQuery struct {
	query    string
	has_URL  bool
	URL      string
	has_addr bool
	addr     address
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
	contents address
}

func (a Addr) isCorpus() bool {
	return true
}

type iQuery struct {
	query  string
	corpus Corpus
}
