.PHONY: all build install test clean

all: build

build:
	dune build

install:
	dune install

test:
	dune test

clean:
	dune clean

run-server:
	dune exec autoprover server

prove:
	dune exec autoprover prove "$(THEOREM)"

# Build native with optimizations
native:
	dune build --profile release
	
# Extract from Coq
extract:
	coqc -R theories AutoProver theories/*.v
	
.DEFAULT_GOAL := all