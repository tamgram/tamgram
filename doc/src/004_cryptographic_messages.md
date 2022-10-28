# Cryptographic messages

Tamarin operates in the symbolic model, this means
cryptographic messages are modeled
as terms instead of bitstrings.

Tamgram largely replicates Tamarin with regards
to construction of messages (or terms):
a term is (exclusively) one of the following:
- a constant
- a "cell"
- `f(x0, ..., xn)` for some
n-ary function symbol f to terms `x0`, ..., `xn`

## Constants and cells

We first discuss names which do not
follow lexical scoping.

First category is public constants, which
are referenced by either `$A` for arbitrary
identifier `A`,
or `"str"` for arbitrary string `str`.
This is exactly the same as Tamarin's public constant
but we use double quotes instead of single quotes
as the latter are reserved for cells.
There is no scoping rules for these terms
and one may make use of them anywhere
in the specification.
In other words, we may consider them
to always exist in the global scope.

Second category is cells,
which are referenced by `'c` for arbitrary identifier `c`.
Syntactically, users may only make use of them in
processes, as there is no meaningful interpretation
when referenced in lemmas and so on.

As mentioned before,
cells behave as keys to a process-local lookup table.
One can make use of keys wherever a term is expected inside
the process (including action facts).

While these do not follow the lexical scope,
their "lifetime" is checked by Tamgram to ensure
the usage of cells must be well defined.
To do this, Tamgram overapproximates
the possible traces/executions of a process
(ignoring restrictions and whether the premise
of the rule can actually be fulfilled),
and ensures that all cells are well defined
(by the `:=` assignment syntax)
before use.

## Uninterpreted function symbols

Tamgram recognizes the same builtins as illustrated in the section with our first example.
Tamgram similarly allows for user specified uninterpreted function symbols:

```
fun f/2
fun hash/1
```

Additionally Tamgram requires uninterpreted predicate symbols (multiset fact/proposition constructors)
and uninterpreted action predicate symbols (action fact/proposition constructors) to be declared similarly,
as we consider this to be necessary to avoid typos which can
still pass Tamarin's wellformedness checks.

```
pred Token/2
pred !Ltk/2

apred Start/2
apred Stop/2
```

`pred` is for predicates, result of which
can only be used in left (premise) or right (conclusion) side
of a rule.

`apred` is for action predicates, result of which
can only be used in the action field (label) of a rule.

`pred !P` for some symbol `P` is for persistent predicates,
result of which can only be used in left or right side
of a rule, and must be prefixed with the `!` unary operator.
`apred !P` denotes similar meaning.

Above symbols are "uninterpreted" by Tamgram as they are compiled
as is (with name mangling to avoid collision) to Tamarin.

Interpreted symbols are function macros which are evaluated by Tamgram.

## Term macros

The most general form of macro declaration is via the `let f(...) : typ = ...` syntax:

```
let f(x : bitstring, k : bitstring) : bitstring =
  enc(<x, x>, k)
```

Alternatively one can make use of the following shorthands:

- `fun f(...) = ...` is shorthand for `let f(...) : bitstring = ...`
- `pred f(...) = ...` is shorthand for `let f(...) : prop = ...`
- `apred f(...) = ...` is shorthand for `let f(...) : aprop = ...`

Usually the above shorthands suffice, but in
cases where one needs expansion into a formula
(making use of quantifier),
`let f(...) : formula = ...` is the only way.

Type checking is straightforward
as there is no "smart" type inference
- any parameter missing type annotation just defaults to `bitstring`.

In addition to module level macros,
Tamgram also supports local macros which
can be declared within a term, a rule, or a process as well,
but these are restricted to the `let f(...) : typ = ... in` syntax,
where `let f(...) = ... in` is the only shorthand that picks `bitstring` for
the return type.

```
let f(x : bitstring, k : bitstring) : bitstring =
  let f'(x) = <x, x> in
  enc(f'(x), k)
```

## Restrictions of term macros

Cells (or names typed `cell`) cannot be used within a term macro body,
and as such term macros cannot treat cells
differently, such as by using them in assignment syntax (`:=`).

In other words, one can pass cells to term macros as if it is
a typical value,
but term macros cannot possibly change the content of the cells.

This is largely to facilitate reading of specification by ensuring
all term macro invocations are "side-effect free".

It is also worth noting that these macros
are restricted to the syntax space of terms.
If we wish to make use of process syntax
(and change cell content),
we will need to use process macros.

We will discuss process macros in the process section.
