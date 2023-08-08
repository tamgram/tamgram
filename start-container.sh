#!/bin/bash
podman run -it \
  -v ~/tamgram:/home/opam/tamgram \
  --userns keep-id:uid=$(id -u),gid=$(id -g) \
  --rm \
  localhost/tamgram
