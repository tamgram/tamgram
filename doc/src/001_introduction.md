# Introduction

Tamgram is a frontend to the Tamarin prover that aims
to provide a more ergonomic experience especially to large scale
specification of protocol.

Tamgram aims to accomodate the full expressiveness of Tamarin's syntax
and provide sensible static checks on top of them, which should
subsume most of of Tamarin's wellformedness check - if Tamgram
compiles successfully, Tamarin should not report egregious wellformedness
problems with the compiled output.
One known exception to this right now is guardedness check of
lemmas and restrictions - this will be addressed in a later release.

This manual is aimed at audience with some familiarity with
Tamarin.

Please note that the document uses the following pairing of terms
interchangably:

- "attacker" and "adversary"
