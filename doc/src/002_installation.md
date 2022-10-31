# Installation

## Recommended

The recommended route to installation is to use the provided statically linked binary.

## Building via container

One can build the container image used by `podman build .` at repo root,
and use `make` or `make release-static` to yield the binary.

## Building from scratch

This requires OCaml version >= 4.14 (it may work for older version, but
we have not tested any),
and the following command to first install the relevant dependencies

```
opam install dune containers fmt menhir utop ocp-indent ansiterminal
```

followed by

```
make
```

or

```
dune build @all
```
