FROM docker.io/ocaml/opam:alpine-ocaml-5.1

USER root
RUN apk add linux-headers

USER opam
RUN opam-2.2 init --disable-sandboxing
SHELL ["/bin/bash", "--login" , "-c"]
RUN opam-2.2 install dune
RUN opam-2.2 install utop ocp-indent

USER root
COPY . /home/opam/tamgram
RUN chown -R opam:opam /home/opam/tamgram

USER opam
WORKDIR /home/opam/tamgram
RUN dune build tamgram.opam
RUN opam-2.2 install . --deps-only
