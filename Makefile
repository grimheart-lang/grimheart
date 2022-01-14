dev-switch:
	opam switch create -y ./ ocaml-base-compiler --deps-only --with-test

clean:
	dune clean

build:
	dune build

test:
	dune runtest -f

coverage:
	dune runtest --instrument-with bisect_ppx -f
	bisect-ppx-report html

format:
	dune build @fmt --auto-promote
