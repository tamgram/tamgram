# Static analysis

## Invalid cell reference

To rule out invalid cell references,
Tamgram overapproximates
the possible traces/executions of a process
(ignoring restrictions and whether the premise
of the rule can actually be fulfilled),
and ensures that all cells are well defined
(by the `:=` assignment syntax)
before use.

This procedure is sound, but not complete.
As such there are cases where invalid cell references
cannot actually occur but Tamgram would still
rule as invalid.

We may support user-specified assertion
of some invalid cell access not being
possible in a later release,
and emits the relevant lemma
for proving said impossibility
instead of failing compilation altogether.

## Impossible cell pattern matches

Tamgram tries to statically analyze to some extent (again based
on overapproximation of process execution),
and for cases where it is confident a match is not possible,
compilation yields an error.

For instance, if we swap the positioning of `'a` and `'b`
in the third step:

```
builtins := hashing

process A =
  [ Fr(~k) ]-->[ 'a := "A", 'b := "B", 'h := h(<"A", "B", k>) ];
  []-->[ 'x := <'a, 'b, 'h> ];
  [ 'x cas <'b as x, 'a as y, 'h as z> ]-->[ Out(x), Out(y), Out(z) ]
```

We get

```
File "test.tg", line 6, character 5
6 |   [ 'x cas <'b as x, 'a as y, 'h as z> ]-->[ Out(x), Out(y), Out(z) ]
         ^
Error: cell 'x never matches pattern <'b, 'a, 'h>
```

This is mainly for ruling out mismatching
of cell content especially during non-deterministic choices.
A typical pattern would be modelling of a state machine
via the use of a state label
that is used to decide the transition to take:

```
process A =
  []-->[ 'st := "St0" ];

  entry_point "main";

  choice {
    { [ 'st cas "St0" ]-->[ 'st := "St1" ] };
    { [ 'st cas "St0" ]-->[ 'st := "St2" ] };
    { [ 'st cas "St2" ]-->[ 'st := "St1" ] };
    { [ 'st cas "St3" ]-->[ 'st := "St1" ] };
  };

  goto "main"
```

```
File "impossible_pattern0.tg", line 10, character 9
10 |     { [ 'st cas "St3" ]-->[ 'st := "St1" ] };
              ^
Error: Cell 'st never matches pattern "St3"
```

We may add an additional check of unused cell data
(`'st := "St1"` above for instance).
