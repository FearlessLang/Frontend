# Differences from the paper

The repository Frontend implements the formal model of the paper with the extensions below.

## 1. Methods overloaded on their capability

Paper: method names in a literal are disjoint (A2), and `meth(D[Ts], m)` looks a method up by
name.
Frontend: A method is identified by its name and its capability: a literal can declare both
`imm .get` and `mut .get`, and a call names the capability it calls, `e.m[rc](..)`. Method
tables, `sources` and overriding are keyed on `(m, rc)`.

## 2. Overriding refines nominal types

Paper: `overrideOk` requires `mtype1 ~= mtype2`, identical parameter and result types.
Frontend: co-contra variant refinement is allowed.
The outermost capabilities stay fixed because they are impacted by promotions

## 3. Type arguments are equal up to single capability spellings

Paper: `RC-sub` requires `T[mut] = T'[mut]`, comparing type arguments as written.
Frontend: different writing for some types are considered identical. For example imm X and X with [X:imm] ( see `eqModVar`)
Sound: every instantiation of `X` gives all those spellings the same type.

## 4. A literal is typed iso when it could be written iso

Paper: `Lit-t` gives `[Ts] R L` the type `R D[Ts]`.
Frontend: iso is inserted in some hardcoded sound cases, all those are cases where if iso was already present in the code, it would have been valid.

## 5. Type expressions

Paper: expressions are bindings, calls and literals.
Frontend: for performance reasons, a 'type expression' is added; it should behave exactly as using the type name as a literal in the paper, but avoids the desugaring from generating a large amount of pointless anon types.

## 6. Capture free declarations, Sealed, BaseId and other magic interfaces

Not in the paper. They will restrict how the type system work and can have impact on code generation.

## 7. Better errors
Frontend may deliver more early errors, for example requiring more things to not be dead code.

## 8. use/map/packages etc

Frontend offers ways to handle large scale software while the paper focus on the core calculus.
Those are all about code structure and mapping names in more conventient names.
