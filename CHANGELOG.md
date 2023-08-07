# Changelog

## 0.5.1

- Fixed cell location used in missing `rw` marker error message

## 0.5.0

- Added named arguments to process macro and term macro

  - Usage for term macro:
    ```
    fun f (named a, named b) = <a, b>

    process A =
      []->[ Out(f(a is "1", b is "2")) ]
    ```

  - Usage for process macro:
    ```
    process f (named 'a, named b) = []->[ Out(<'a, b>) ]

    process A =
      []->[ 'c := "1" ];
      f('a is 'c, b is "2")
    ```

- Added read write marker to cell input in process macro syntax
  ```
  process f(rw 'a, 'b) = []->[ Out(<'a>), 'a := 'b ]
  ```

- Replaced module `insert` keyword with `include`

- Added `import` syntax to import top level modules (other files)

- Added module alias syntax `module A = A.B.C`

- Added uninterpreted function symbols with explicit arguments,
  which behave like record types

## 0.4.3

- Fixed constant string literal checking to allow `_`

## 0.4.2

- Simplified cell data shape analysis heavily to reduce false negatives

- Added missing check for constants of the form `"..."`

## 0.4.1

- Added special consideration for cell data shape when value is a number

## 0.4.0

- Added `if-then-else` syntax

## 0.3.0

- Renamed styles:

  - `frame-minimal-reversed-linking0` to `frame-minimal-backward0`

  - `mix0` to `frame-minimal-hybrid0`

- Replaced `goto` with `while` and `loop` loops

## 0.2.0

- Base version

