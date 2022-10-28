# Processes

A protocol, or a system, is specified in Tamgram as
a collection of processes.
We illustrate the three main constructor syntax of a process here.

Obviously, all of the following control flow structures
can obviously be manually crafted as seen in existing case studies,
i.e. "next step" transitions, non-deterministic choices, loops,
but adjustment on the states is made very error prone when
the encoding is done manually.

## Rule or step

The basic building block of a process is a multiset rewriting rule.

A rule in Tamgram is very similar to a rule in Tamarin, but with
the addition of cells as seen in the initial example.

There are three main ways of using cells which we make precise here

### Direct reference of cell

As seen in the initial example, we may simply write `'c` for some cell `c`
wherever a term is expected.
Semantically this substitutes `'c` by whichever cell-free term
is indexed `'c`.

### Cell assignment

Also seen in our initial example, we have the assignment `:=` syntax,
where it is syntactically restricted to only accept a single cell on left side,
and may only appear on the right side of a rule.

There may be confusion about how it interacts with
references of the same cell inside a rule, for instance:

```
process A =
  []-->[ 'a := "1" ];
  []-->[ Out('a), 'a := "2" ]
```

Is "2" or the old value of `'a` ("1") used in `Out`?

The semantics we've chosen is that all assignments
only come into effect starting from following rule,
i.e. assignments are always "pushed" to the after
the current rule. Additionally a cell may be assigned at most once in a rule.

Thus in the above rule, the old value ("1") is emitted,
then `'a` is updated to "2".

This overall maintains the intuition of lack of ordering
during consideration of multisets.

### Cell pattern matching

We observe frequent use of pattern matching within a state fact
in existing case studies usually in order to access
inner terms of, for instance, a tuple.
And sometimes multiple terms in the state fact store
share some subterms (implying equality).

To retain this expressive power, we introduce
the "cell as" syntax, `'c cas t` for some cell `c` and
term `t`.

We write a simple example below where we store
a triple into `'x` and retrieve the three
inner terms later.

```
builtins := hashing

process A =
  [ Fr(~k) ]-->[ 'a := "A", 'b := "B", 'h := h(<"A", "B", k>) ];
  []-->[ 'x := <'a, 'b, 'h> ];
  [ 'x cas <a, b, h> ]-->[ Out(a), Out(b), Out(h) ]
```

One may also use content of other cells
during pattern matching as long
as there are no cyclic dependencies.
One can additionally bind the subterm via the `as` syntax
for brevity if needed.

```
builtins := hashing

process A =
  [ Fr(~k) ]-->[ 'a := "A", 'b := "B", 'h := h(<"A", "B", k>) ];
  []-->[ 'x := <'a, 'b, 'h> ];
  [ 'x cas <'a as x, 'b as y, 'h as z> ]-->[ Out(x), Out(y), Out(z) ]
```

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

## Sequential composition

We have seen the sequential composition of
some simple steps above via the `;` syntax.
In Tamgram, sequential composition
also works for two arbitrary proceses `A`, `B`
by `A; B` syntax.
Similar to executing
a series of statements programming, `A` is first run
then `B` is run.
Underneath,Tamgram does this by inserting the state
facts when appropriate (similar to a manual encoding).

Following example "chains" two rules together,
with a key generated in step 1 stored
later for use in step 2.

```
builtins := hashing

process C =
  [ Fr(~k), In(x) ]-->[ Out(h(<k, x>)), 'k := k ];
  [ In(x) ]-->[ Out(h(<x, 'k>)) ]
``` 

## Non-deterministic choices

Multiple possible flow of execution is
a basic and necessary primtive in computation,
and this naturally extends
to specification of state transitions or in
some form of programming (e.g. `if else, switch`).

Non-deterministic choices can be made deterministic,
but not the other way around easily,
as such we focus on composable
primitive for providing non-deterministic choices.

In Tamarin, non-deterministic choices can be achieved by specifying
multiple rules which consume the same state fact
(or same multiset of facts, more generally speaking),
similarly to drawing out the multiple branches for a vertex
in a state transition diagram. For example:

```
rule A1:
    [ Fr(~k) ]-->[ StA1(~k) ]

rule A2a:
    [ StA1(~k), In(x) ]-->[ Out(h(<~k, x>)) ]

rule A2b:
    [ StA1(~k), In(x) ]-->[ Out(aenc(x, ~k)) ]
```

`A2a` and `A2b` are two possible steps stemming from A1
with different outputs.

However, manual specification of choices becomes complicated
as the system grows
in size, when we nest multiple layer of choices,
and when we wish to sequentailly compose another
segment of computation after any of the choices has
been executed.

To illustrate, we write out a simple example in
Tamgram, and show the corresponding compiled Tamarin rules
which gives a fairly close depiction of what an
equivalent manual encoding entails.

In Tamgram, multiple choices are specified using syntax
`choice { { P1 }; ...; { Pn } }` where each
`Pi` is a process.

```
builtins := hashing

process A =
  choice {
    {
      [ In("A") ]
      -->
      [ Out(h("A")) ]
    };
    {
      choice {
        {
          [ In("B")
          , In(x) ]
          -->
          [ Out(h(<"B", x>)) ]
        };
        {
          [ In("C")
          , In(x) ]
          -->
          [ Out(h(<"C", x>)) ]
        };
      };

      [ In(x) ]-->[ Out(h(<x, x>)) ]
    };
  };

  choice {
    {
      [ In("D")
      , In(x) ]
      -->
      [ Out(h(<"D", x>)) ]
    };
    {
      [ In("E")
      , In(x) ]
      -->
      [ Out(h(<"E", x>)) ]
    };
  }
```

Compiled result

```
```

It is perhaps worth noting that with differing depth of the `choice` tree,
manual encoding is especially prone to errors and adjustment of
the manual encoding is significantly more difficult than relying on Tamgram.

### Example of impossible cell pattern matching

We first write a working example to serve as reference:

```
builtins := hashing, symmetric-encryption

process A =
  choice {
    { []-->[ 'x := "a" ] };
    { []-->[ 'x := h("b") ] };
    { [ Fr(~k) ]-->[ 'x := senc(h(k), k) ] };
    { []-->[ 'x := h(<"a", "d">) ] };
  };

  choice {
    { [ 'x cas "a" ]-->[ Out("Ok") ] };
    { [ 'x cas h(_) ]-->[ Out("Ok") ] };
    { [ 'x cas h("b") ]-->[ Out("Ok") ] };
    { [ 'x cas senc(_, _) ]-->[ Out("Ok") ] };
    { [ 'x cas senc(h(_k), _k) ]-->[ Out("Ok") ] };
  }
```

The above code is accepted by Tamgram,
next we examine some example additions we can make to the second
choice tree to yield an error.

**A simple impossible direct string literal**

```
builtins := hashing, symmetric-encryption

process A =
  choice {
    { []-->[ 'x := "a" ] };
    { []-->[ 'x := h("b") ] };
    { [ Fr(~k) ]-->[ 'x := senc(h(k), k) ] };
    { []-->[ 'x := h(<"a", "d">) ] };
  };

  choice {
    { [ 'x cas "a" ]-->[ Out("Ok") ] };
    { [ 'x cas h(_) ]-->[ Out("Ok") ] };
    { [ 'x cas h("b") ]-->[ Out("Ok") ] };
    { [ 'x cas senc(_, _) ]-->[ Out("Ok") ] };
    { [ 'x cas senc(h(_k), _k) ]-->[ Out("Ok") ] };
    { [ 'x cas "b" ]-->[] };
  }
```

yields

```
File "test.tg", line 17, character 9
17 |     { [ 'x cas "b" ]-->[] };
              ^
Error: cell 'x never matches pattern "b"
```

**Impossible shape**

```
builtins := hashing, symmetric-encryption

process A =
  choice {
    { []-->[ 'x := "a" ] };
    { []-->[ 'x := h("b") ] };
    { [ Fr(~k) ]-->[ 'x := senc(h(k), k) ] };
    { []-->[ 'x := h(<"a", "d">) ] };
  };

  choice {
    { [ 'x cas "a" ]-->[ Out("Ok") ] };
    { [ 'x cas h(_) ]-->[ Out("Ok") ] };
    { [ 'x cas h("b") ]-->[ Out("Ok") ] };
    { [ 'x cas senc(_, _) ]-->[ Out("Ok") ] };
    { [ 'x cas senc(h(_k), _k) ]-->[ Out("Ok") ] };
    { [ 'x cas senc(h(h(_k)), _k) ]-->[ Out("Ok") ] };
  }
```

yields

```
File "test.tg", line 17, character 9
17 |     { [ 'x cas senc(h(h(_k)), _k) ]-->[ Out("Ok") ] };
              ^
Error: cell 'x never matches pattern senc(h(h(_k)), _k)
```

## Loops

One final important primitive are loops (or jumps).
We note that encoding of a naive case such as
a process with only one outer loop is straightfoward.
However, with jumps only occuring in certain choices
(for instance "breaking" a loop if some condition is met,
or just a while loop in general),
encoding the transitions manually
becomes non-trivial.

In Tamgram, possible jump points are denoted
by `entry_point "label"`,
jumps to entry points are denoted by `goto "label"`.
To reduce complexity of static analysis and facilitate
more readable Tamgram files, jumps are restricted to
backwards - entry point must have appeared earlier in
the process.

Similarly we write a simple example in Tamgram and show
the compiled results.

```
builtins := multiset

apred Neq/2
apred Eq/2

restriction Inequality =
  All x y #i. Neq(x, y) @ i ==> not(x = y)

restriction Equality =
  All x y #i. Eq(x,y) @ i ==> x = y

apred RightGuess/1

process GuessingGame =
  let answer = "F" in
  
  // Output some possible answers
  []-->[Out(<"A", "B", "C", answer>)];
  
  // Some persistent states
  []-->['try_count := "0"];
  
  entry_point "start";
  
  choice {
    {
      /*	We proceed if we receive the right answer
          from network
      */
      [In(x)]--[Eq(x, answer)]
      -->
      ['try_count := 'try_count+"1"]
    };
    {
      /* 	Otherwise we count the try and go back to
          start
      */
      [In(x)]--[Neq(x, answer)]
      -->
      ['try_count := 'try_count+"1"];
      goto "start"
    };
  };
  
  []--[ RightGuess('try_count) ]-->[ ]

lemma at_least_one_guess =
  All x #i.
    RightGuess(x)@i ==> not (x = "0")

lemma possibly_2_guesses =
  exists-trace
  Ex #i.
    RightGuess(("0"+"1")+"1")@i

lemma eventually_right_guess =
  exists-trace
  Ex x #i.
    RightGuess(x) @ i
```

Compiled output

```
theory guess
begin

builtins: multiset

restriction Inequality:
  "All x_16 y_17 #i_18 .
     ((Neq_14(x_16, y_17) @ #i_18) ==> (not ((x_16) = (y_17))))"

restriction Equality:
  "All x_20 y_21 #i_22 .
     ((Eq_15(x_20, y_21) @ #i_22) ==> (((x_20) = (y_21))))"

rule TgStartGuessingGame_28_0:
  [Fr(~pid)]--[]->[St(~pid, 'tgk0', 'empty_tuple')]

rule TgRuleGuessingGame_28_0to1:
    [ St(~pid, 'tgk0', 'empty_tuple')
    ]
  --[ 
    ]->
    [ St(~pid, 'tgk1', 'empty_tuple')
    , Out(<'A', 'B', 'C', 'F'>)
    ]

rule TgRuleGuessingGame_28_1to2:
  [St(~pid, 'tgk1', 'empty_tuple')]--[]->[St(~pid, 'tgk2', <'0'>)]

rule TgRuleGuessingGame_28_2to3:
  [St(~pid, 'tgk2', <tgsys44>)]--[]->[St(~pid, 'tgk3', <tgsys44>)]

rule TgRuleGuessingGame_28_3to4:
    [ St(~pid, 'tgk3', <tgsys38>)
    , In(x_26)
    ]
  --[ Eq_15(x_26, 'F')
    ]->
    [ St(~pid, 'tgk4', <((tgsys38) + ('1'))>)
    ]

rule TgRuleGuessingGame_28_3to5:
    [ St(~pid, 'tgk3', <tgsys42>)
    , In(x_27)
    ]
  --[ Neq_14(x_27, 'F')
    ]->
    [ St(~pid, 'tgk5', <((tgsys42) + ('1'))>)
    ]

rule TgRuleGuessingGame_28_4to7:
  [St(~pid, 'tgk4', <((tgsys39) + ('1'))>)]--[RightGuess_24(((tgsys39) + ('1')))]->[]

rule TgRuleGuessingGame_28_5to6:
  [St(~pid, 'tgk5', <((tgsys43) + ('1'))>)]--[]->[St(~pid, 'tgk6', <((tgsys43) + ('1'))>)]

rule TgRuleGuessingGame_28_6to3:
  [St(~pid, 'tgk6', <tgsys44>)]--[]->[St(~pid, 'tgk3', <tgsys44>)]

lemma at_least_one_guess []:
  all-traces
  "All x_29 #i_30 .
     ((RightGuess_24(x_29) @ #i_30) ==> (not ((x_29) = ('0'))))"

lemma possibly_2_guesses []:
  exists-trace
  "Ex #i_32 .
     RightGuess_24((((('0') + ('1'))) + ('1'))) @ #i_32"

lemma eventually_right_guess []:
  exists-trace
  "Ex x_34 #i_35 .
     RightGuess_24(x_34) @ #i_35"

end
```

## Process macros

Process macros allow access to the process syntax space,
and allow "subroutine" calls essentially.
These macros, similar to term macros,
are hygienic syntactic macros.

This feature is motivated by
the use of what is meaningfully process macros
appear in existing case studies through the use of
text preprocessor/macro systems such as m4.
However, those are closer to textual expansion
where (lexical) scoping needs to be carefully
curated by use of appropriate prefixes for names.

For instance we can declare an output encryption macro
and use it in two separate processes below.

```
builtins := symmetric-encryption

process out_enc(m, k) =
  []-->[ Out(senc(m, k)) ]

process A =
  [ Fr(~k) ]-->[ 'k := k ];
  out_enc("A1", 'k);
  out_enc("A2", 'k)

process B =
  [ Fr(~k) ]-->[ 'k := k ];
  out_enc("B1", 'k);
  out_enc("B2", 'k)
```

We can see in this case it is a simple
AST expansion in the following compiled output.

```
```

If we wish to also abstract away nonce increment/refresh,
we can make use of "cell arguments", which allow
us to specify assignments to them,
similar to "pass by reference".
The syntactic requirement is to ensure any non-side effect free
usage is visible up front - a process
macro does not modify any process state if it contains
no cell arguments.

```
builtins := symmetric-encryption

process out_enc(m, k, 'n) =
  [ Fr(~n) ]-->
  [ Out(senc(<m, 'n>, k)), 'n := n ]

process A =
  [ Fr(~k), Fr(~n) ]-->[ 'k := k, 'n := n ];
  out_enc("A1", 'k, 'n);
  out_enc("A2", 'k, 'n)

process B =
  [ Fr(~k), Fr(~n) ]-->[ 'k := k, 'n := n ];
  out_enc("B1", 'k, 'n);
  out_enc("B2", 'k, 'n)
```

The compiled output becomes slightly more complex
this time since we require modification of
process context.

```
```

where we see in `TgRuleA_22_1to2` and `TgRuleB_25_5to6`
the new nonce replaces the old nonce in the passed context tuple
correctly.

Achieving similar results in manual encoding requires
careful choice of prefixes and naming schemes
from our observation.
