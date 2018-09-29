Nazo ML (nml)
=============

This is an experimental implementation of temporal-logic-based Hindley-Milner type system.

This is (currently) not for practical use.

# Summary

In NML, technically, there are three temporal modal operators: Next(○), Finally(◇), and Globally(□).

The basic idea of NML's type system is that every non-temporal type is □-type.

This restriction makes it able to explicitly insert ```run``` when we want to "lift" ("fmap", or whatever) a function and then apply it to a delayed (quoted) term.

# Non-formal explanation

## Delayed term/type

```(@ 1 @)``` has type ```Next[1] Nat```, which means that we can obtain a ```Nat``` value at the next stage.

Also, ```<@ 1 @>``` has type ```Finally Nat```, which means that we can obtain a ```Nat``` value at *some stage in the future*. So, ```Finally Nat``` essentially means ```Next[inf] Nat```.

## Lifted let expression

```
let-next x = (@ 1 @) in
if eq x 0 then
  true
else
  false
```

is the equivalent of

```
let x = (@ 1 @) in
(@
  if eq (run[1] x) 0 then
    true
  else
    false
@)
```

, delays the computation, and thus has type ```Next[1] Bool```.

Similarly,

```
let-finally x = <@ 1 @> in x + 1
```

is the equivalent of

```
let x = <@ 1 @> in <@ (run[inf] x) + 1 @>
```

and has type ```Finally Nat```.

## Useful example: I/O

The classical "scan" function can be thought as a function that returns a delayed value.

```
> readNat;;
type: Unit -> Next[1] Nat
```

Now we can use this like:

```
let-next x = readNat () in
let-next y = readNat () in
let-next z = readNat () in
(x + y) * z
```
## Subtyping by stage

In NML, there is a built-in subtyping relation based on stage:

```
a <: Next[1] a <: Next[2] a <: ... <: Next[inf] a = Finally a
```

This means that, for example, a function with type ```Finally a -> b``` can also be applied to a value with type ```Next[n] a``` for any ```n```, including ```0``` (= ```a```).

See further example below:

![subtyping example](https://i.imgur.com/SV5SO84.jpg)

## NML and real-world linearity

The execution of a NML program is defined as 

```
eval :: Next[n] a -> a (for any n in [0,inf])
eval program = run[inf] program
```

Each computation in each stage is kept pure functional:

* Everything impure will be done between discrete time stages.
* Once the stage is successfully transited, the computation at the current stage will certainly finite. 

This ensures the linearity of the whole execution, while

* allowing non-strict evaluation inside stages (because they are pure): lazy evaluation and even partial evaluation
* not relying on specific compiler magics (such as ```RealWorld``` in GHC)

Also, it should be doable to express parallel computation in this type system as

```
parallel :: List (Finally a) -> Finally (List a)
```

, and I'm currently investigating it.

# TODO

## Practical things

- [x] Polymorphism
    - [x] Let expressions
    - [x] Type operators (eg. tuples)
    - [x] Forall quantifier
- [x] Variants
    - [x] With type parameters
- [x] Inductive data types (extends variant types)
    - [x] Well-founded recursive functions (```fixpoint```)
- [x] Pattern matching (```match```)
    - [x] Exhaustiveness check
    - [x] Matching functions (```function```)
- [x] Operators
    - [x] Operator definitions (```let (+) l r = ...```)
    - [x] Use as a function
- [x] Top-level expressions
    - [x] Let/Do expressions
    - [x] Type definitions
    - [x] Define/Open modules
    - [x] On REPL

## Type system extensions

- [x] Next(○) type operator (``` Next[1] T ```)
    - [x] Code quotation (```(@ t @)```)
    - [x] Lifted let expression (```let-next```)
    - [ ] Macros (```macro```)
- [ ] Dependent types
    - [ ] Length-dependent List
    - [ ] Compile-time type generation
- [ ] Refinement types
    - [ ] Assertions
- [x] Finally(◇) type operator (```Finally T```, ```<@ t @>```, ```let-finally```)
    - [ ] Infinite recursive functions
    - [ ] Asynchronous computation

## Runtime improvements
- [x] REPL
    - [x] Line editor
    - [x] Suggestions & completions
    - [x] Load and execute source files
    - [x] Import sources on the fly
- [ ] Compiler
- [ ] Interop
    - [x] Built-in functions written in F# 
    - [ ] Call .NET methods directly

# License

GPL v3

