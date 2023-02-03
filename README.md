# Tamgram

A Frontend for Large-scale Protocol Modeling in Tamarin

[User manual](https://darrenldl.github.io/tamgram/)

## Tamarin container

See [here](https://github.com/darrenldl/tamarin-prover-container) for ready-to-use
Tamarin container images.

A typical usage (assuming you've cloned this repository into your home directory)
would look like:

```
podman run -dt -v ~/tamgram:/root/tamgram --rm docker.io/darrenldl/tamarin-prover:1.6.1
```

and then enter directory `/root/tamgram` when in container.
