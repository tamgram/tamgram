# Static analysis

## Invalid cell reference

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
of cell content especially during non-deterministic choices,
which we will see an example below.

