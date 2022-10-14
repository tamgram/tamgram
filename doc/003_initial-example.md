# Initial example

This section follows Tamarin's initial example section closely,
but introduces Tamgram syntax, features, and differences when appropriate.
The syntax overall leans closer to ML or other programming languges.

It may be useful to read this with chapter 3 of the original manual
side by side.

We start with the same simple protocol that consists of two messages,
written in the the same so-called Alice-and-Bob notation:

```
C -> S : aenc(k, pkS)
C <- S : h(k)
```

A Tamgram file ends with `.tg` extension, and does not start with a `theory` header,
instead we immediately start specification of protocol.

This simplication is in some way to reduce overhead for multi file projects.
We will revisit how to span your specification across multiple (nested) modules
and files in a later chapter.

The following example is stored as `doc/code/FirstExample.tg`,
which can be compiled into Tamarin file via

```
tamgram compile doc/code/FirstExample.tg output_file
```

If `output_file` is `-`, then Tamgram prints to stdout instead.

If `output_file` is a directory, then Tamgram writes to `output_file/input_file.tg.spthy` instead.

## Cryptographic primitives

Tamgram passes through the same set of builtins as Tamarin.

The following code from the example tells Tamgram to note
the relevant builtins when compiling to tamarin file.

```
builtins := hashing, asymmetric-encryption
```

Tamgram then inserts the relevant (reserved) names into the lexical scope.

The names are also checked statically within Tamgram.
For instance, if we mistyped `hashing` as `hashng`, we would receive the
following error message:

```
File "FirstExample.tg", line 14, character 12
14 | builtins := hashng, asymmetric-encryption
                 ^
Error: unrecognized builtin hashng
```

## Modeling a Public Key Infrastructure

In the original manual, we would be writing mutliset rewriting rules immediately.
However, in Tamgram, most names must be declared first and follow lexical scopes
(we will discuss the exceptions as they appear).

We can declare `Ltk` and `Pk`, which we intend to as a constructor of persistent multiset terms
as follows:

```
pred !Ltk/2
pred !Pk/2
```

which reads predicate `Ltk` with arity of 2, and the same for `Pk`

We can now begin to model registration of public keys:

```
process Register_pk =
  [ Fr(~ltk) ]
  -->
  [ !Ltk($A, ~ltk), !Pk($A, pk(~ltk)) ]
```

In Tamgram, all forms of progression are modeled as process - a rule in Tamarin
becomes a singleton process as shown above.
For now, it suffices to think of process as a list of rules -
we apply each rule one after another.
In other words, we can consider a rule a step in the process.

A rule has at least two fields, the left (the premise) and
right (the conclusion).
The premise picks (or pattern matches)
the multiset of facts the rule consumes
from the state of the world (or system),
the conclusion denotes the resulting
addition to the state of the system.

Tamgram uses the same prefixes for specifying the sort (or type) of variables/names.

- `~x` is a shorthand for `x : fresh`
- `$x` is a shorthand for `x : pub`
- `#i` is a shorthand for `x : temporal`
- `m`  is a shorthand for `m : bitstring`
  (names default to type `bitstring`)

String constants are specified using double quotes (`"..."`) instead
of single quotes (`'...'`) as single quotes are used as a prefix for
another type of names called "cell", which we will use
shortly to handle states.

The explanation of the above rule is then as follows.
First we generate/pick a fresh name `~ltk` via use of
the reserved predicate `Fr`
(premise of `Fr(...)` are handled specifcially by Tamarin),
and record it as long-term private key of A via `!Ltk($A, ~ltk)`
and derive the public key `pk(~ltk)`
and record said public key via `!Pk($A, pk(~ltk))`.

Same in Tamarin, facts by default
are "linear", and a fact is only
"persistent" when used with the unary operator `!`.
The distinction is that linear facts can only be consumed
by a step/rule from a process
exactly once, while
persistent facts can be consumed arbitrary many times.

It is also worth noting that the `~` prefix (or `: fresh` type annotation)
is not optional for name in `Fr(...)` in Tamgram.
If we remove the prefix as follows:

```
process Register_pk =
  [ Fr(ltk) ]
  ...
```

the file would fail to type check:

```
File "FirstExample.tg", line 21, character 9
21 |     [ Fr(ltk) ]
              ^
Error: expected type fresh for term ltk : bitstring, got bitstring instead
```

Next, we model retrieval of public key by adversary.

```
process Get_pk =
  [ !Pk(A, pubkey) ]
  -->
  [ Out(pubkey) ]
```

The process reads a previously stored
public key record (we can think of a `!Pk(..., ...)`
as a global database predicate in that sense),
and outputs the public key via the reserved fact `Out(...)`
which denotes which messages are outputted to the network
or made known to the adversary.

Last part of the setup before the main protocol steps
is the modeling of long-term private key leak.

```
apred LtkReveal/1

process Reveal_ltk =
  [ !Ltk(A, ltk) ]
--[ LtkReveal(A) ]->
  [ Out(ltk) ]
```

The process reads a long-term private key record
and simply outputs it to the attacker.

We notice that it has an extra field in the middle of the arrow (-->),
the facts in this field are called "action facts".
Action facts are facts that label the trace and do not (directly)
talk about the multiset of facts (the state of the system),
contrast this to the premise which
consumes facts,
and conclusion which adds facts.

This labelling allows us to talk about "how" the system
progresses when we state our proof goals, which are called lemmas.

## Modeling the protocol

Now we can revisit the main steps of the protocol

```
C -> S : aenc(k, pkS)
C <- S : h(k)
```

We can model above parties using two processes

```
apred SessKeyC/2

// Start a new process executing the client role, choosing the server
// non-deterministically.
process Client =
    [ Fr(~k)         // choose fresh key
    , !Pk($S, pkS)   // lookup public-key of server
    ]
  -->
    [ 'S := $S  // Store server and key for next step of process
    , 'k := ~k
    , Out( aenc(~k, pkS) )  // Send the encrypted session key to the server
    ];
    [ In( h('k) )       // Receive hashed session key from network
    ]
  --[ SessKeyC( 'S, 'k ) ]-> // State that the session key k
    []                       // was setup with server S

apred AnswerRequest/2

// A server process answering in one-step to a session-key setup request from
// some client.
process Serv =
    [ !Ltk($S, ~ltkS)                             // lookup the private-key
    , In( request )                               // receive a request
    ]
  --[ AnswerRequest($S, adec(request, ~ltkS)) ]-> // Explanation below
    [ Out( h(adec(request, ~ltkS)) ) ]            // Return the hash of the
                                                  // decrypted request.
```

Instead of defining our own state predicate,
we make use of Tamgram specific feature
called "cells" here for handling process local states.

We can think of it as a process local key value table in essence.
This is similar to SAPIC's global lookup table in a sense,
and indeed one can replicate a local lookup table in a global
lookup table by keying with the session (or thread/process) ID,
but restricting the syntax to only handle local states allows
for some optimizations which we will discuss in a separate section.

Same as Tamarin, Tamgram uses C-style comments:
`/*` and `*/` represents block comments,
and `//` represents line comments.

## Modeling security properties

Security properties (in lemmas) are specified over traces
of action facts of the execution of the collection
of Tamgram processes.
The intuition from use of Tamarin carries over
as the translation is fairly staightforward.

We refer reader to the section 3
of the original manual as the lemma
specification in Tamgram
is essentially identitcal to Tamarin.

```
lemma Client_session_key_secrecy =
  /* It cannot be that a  */
    not(
      Ex S k #i #j.
        /* client has set up a session key 'k' with a server'S' */
        SessKeyC(S, k) @ #i
        /* and the adversary knows 'k' */
      & K(k) @ #j
        /* without having performed a long-term key reveal on 'S'. */
      & not(Ex #r. LtkReveal(S) @ r)
    )

lemma Client_auth =
  /* For all session keys 'k' setup by clients with a server 'S' */
    ( All S k #i.  SessKeyC(S, k) @ #i
       ==>
         /* there is a server that answered the request */
       ( (Ex #a. AnswerRequest(S, k) @ a)
         /* or the adversary performed a long-term key reveal on 'S'
            before the key was setup. */
       | (Ex #r. LtkReveal(S) @ r & r < i)
       )
    )

lemma Client_auth_injective =
  /* For all session keys 'k' setup by clients with a server 'S' */
    ( All S k #i.  SessKeyC(S, k) @ #i
       ==>
         /* there is a server that answered the request */
       ( (Ex #a. AnswerRequest(S, k) @ a
           /* and there is no other client that had the same request */
           & (All #j. SessKeyC(S, k) @ #j ==> #i = #j)
       )
         /* or the adversary performed a long-term key reveal on 'S'
            before the key was setup. */
       | (Ex #r. LtkReveal(S) @ r & r < i)
       )
    )

lemma Client_session_key_honest_setup =
  exists-trace
  Ex S k #i.
        SessKeyC(S, k) @ #i
      & not(Ex #r. LtkReveal(S) @ r)
```
