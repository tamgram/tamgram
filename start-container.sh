#!/bin/bash
podman run -it \
  -v ~/tamgram:/home/opam/tamgram \
  --userns keep-id:uid=1000,gid=1000 \
  --rm \
  localhost/tamgram
