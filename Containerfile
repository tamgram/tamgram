FROM docker.io/ocaml/opam:alpine-ocaml-4.14
RUN opam init --disable-sandboxing
RUN opam install dune containers fmt
RUN opam install menhir
RUN opam install utop ocp-indent
RUN opam install ansiterminal
RUN opam install oseq
RUN opam install angstrom
