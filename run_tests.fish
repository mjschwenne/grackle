#!/usr/bin/env fish

echo "Cleaning old tests..."
rm -rf testdata/out/*
echo "Running grackle..."
go run ./cmd/grackle/ -coq-logical-path Grackle.test -coq-physical-path testdata/out/coq/ -proofgen-path testdata/out/pg -go-output-path testdata/out/go -go-package github.com/mjschwenne/grackle/testdata/out/go -goose-output testdata/out/goose/ testdata/proto/calendar
go run ./cmd/grackle/ -coq-logical-path Grackle.test -coq-physical-path testdata/out/coq/ -proofgen-path testdata/out/pg -go-output-path testdata/out/go -go-package github.com/mjschwenne/grackle/testdata/out/go -goose-output testdata/out/goose/ testdata/proto/complete
echo "Checking grackle go..."
go build (find ./testdata/out/go/ -mindepth 1 -maxdepth 1 -type d)
echo "Checking grackle coq..."
rm .rocqdeps.d
make -j(nproc) -s (find testdata/out/coq -name "*.v" | sed -e "s/\.v\$/\.vo/g")
echo "Running grackle tests..."
go test .
