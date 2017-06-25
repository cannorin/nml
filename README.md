Nazo ML (nml) simplified ver.
=============================

This is an experimental implementation of temporal logic based Hindley-Milner type system.

This is (currently) not for practical use.

# Summary

In NML, technically, there are two temporal modal operators: Next(○) and Globally(□).

The basic idea of NML's type system is that every non-○ type is □-type.

This restriction makes it able to explicitly insert ```run``` when we want to "lift" ("fmap", or whatever) a function and then apply it to a delayed (quoted) term.

# Non-formal explanation

## Delayed term/type

```<( 1 )>``` has type ```<Nat>```, which means that we can obtain a ```Nat``` value at the next stage.

## Lifted let expression

```
let! x = <( 1 )> in
if eq x 0 then
  true
else
  false
```

is the equivalent of

```
let x = <( 1 )> in
<(
  if eq (run x) 0 then
    true
  else
    false
)>
```

, delays the computation, and thus has type ```<Bool>```.

## Useful example: I/O

The classical "scan" function can be thought as a function that returns a delayed value.

```
> readNat;;
type: Unit -> <Nat>
```

Now we can use this like:

```
let! x = readNat () in
let! y = readNat () in
let! z = readNat () in
mul (add x y) z
```

Note that each computation in each stage is kept pure functional; everything impure will be done between discrete time stages, and once the stage is successfully transited it is certain that the computation at this stage will finite. 

# TBD

* Inductive data types and well-founded recursive functions
* More practical things such as pattern matching, modules, etc
* Future(◇) operator to describe infinite computation

# License

GPL v3

