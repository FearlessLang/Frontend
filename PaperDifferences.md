# Differences from the paper

The type system implements the formal model of the paper (appendix "Fearless's Formal Model")
with the extensions and restrictions below. Each entry names the paper rule it departs from,
gives the implemented rule and says why it stays sound. Everything not listed here follows the
paper: a difference found elsewhere is either a new entry here or a bug for `TypeSystemBugs.md`.

Notation as in `TypeSystemBugs.md`.

## 1. Methods overloaded on their capability

Paper: method names in a literal are disjoint (A2), and `meth(D[Ts], m)` looks a method up by
name.

A method is identified by its name and its capability: a literal can declare both
`imm .get` and `mut .get`, and a call names the capability it calls, `e.m[rc](..)`. Method
tables, `sources` and overriding are keyed on `(m, rc)`.

Sound: renaming each `(m, rc)` to a fresh name `m_rc` gives a program of the paper.

## 2. Overriding refines nominal types

Paper: `overrideOk` requires `mtype1 ~= mtype2`, identical parameter and result types.

    sigOk(D, cur, par) = same name, capability, type parameters and bounds
                         and forall i. sameOuterRC(D, cur.ts[i], par.ts[i]) and par.ts[i] <: cur.ts[i]
                         and sameOuterRC(D, cur.ret, par.ret) and cur.ret <: par.ret
    sameOuterRC(D, A, B) = A and B have the same outermost capability form, or eqModVar(D, A, B)

Sound: parameters are contravariant and the result covariant, as usual. The outermost
capabilities stay fixed because promotions (`multiMeth`) only rewrite outermost capabilities:
with them fixed, a promotion offered through a supertype is also offered by the type itself.
`TypeSystem.sigSub`.

## 3. Type arguments are equal up to single capability spellings

Paper: `RC-sub` requires `T[mut] = T'[mut]`, comparing type arguments as written.

Type arguments are compared with `eqModVar` (`TypeSystemBugs.md` entries 2 and 15): the
spellings `X`, `rc X` and `read/imm X` of one type variable are the same type argument when
`|D(X)| = 1` and they denote the same capability. Under `D(X) = {mut}`, `Box[X]` and
`Box[mut X]` are the same type; `Box[X]` and `Box[read/imm X]` are not.

Sound: every instantiation of `X` gives all those spellings the same type.

## 4. A literal is typed iso when it could be written iso

Paper: `Lit-t` gives `[Ts] R L` the type `R D[Ts]`.

    promote(R L) = (R = mut or (R in {imm,read} and L has no abstract mut method and no self name))
                   and every binding of G|FTV(Ts) used in the bodies of L has a type T
                   with rcs(D_L,T) subsetOf {iso,imm}, D_L the bounds of L
    promote(R L) implies L is checked and typed as iso L

Sound: when `promote` holds, `Lit-t` accepts `[Ts] iso L`. `discard` keeps every used binding,
since they are all `iso`/`imm`. `callable(iso, mut)` holds, and the `mut` methods it requires
exist: a `mut` literal already has them, and an `imm`/`read` one has no abstract `mut` method.
The self binding is `isoToMut(iso) = mut`, as for a `mut` literal, and an `imm`/`read` literal
promoted has no self name. `TypeSystem.checkLiteral`.

## 5. Type expressions

Paper: expressions are bindings, calls and literals.

`rc C[Ts]` as an expression creates an instance of the declaration `C`; it stands for the
empty literal `[Ts] rc Fresh:C[Ts]{}`, which captures nothing:
- it is typed `iso C[Ts]` when `rc` is `mut`, or `rc` is `imm`/`read` and `C` has no abstract
  `mut` method (as in entry 4), and `rc C[Ts]` otherwise;
- every abstract method of `C` callable at that capability is an error, as the last premise
  of `Lit-t` requires for the empty literal;
- only top-level declarations (self name `this`) and `base.CaptureFree` declarations have type
  expressions; a declaration written inside a method body has none (`typeDeclaredInMethod`).

A declaration with type expressions can be instantiated at any capability, so the `Lit-t`
premise `forall M in Ms. callable(R, rcOf(M))` does not apply to it: a `mut` method of a
top-level `imm` declaration is not dead code. `TypeSystem.checkType`, `checkCallable`.

## 6. Capture free declarations

Not in the paper. A literal implementing `base.CaptureFree` captures nothing: every binding of
`G` is dropped before `Lit-ok`. It is checked once, at the capability it is written with (`imm`
by default), and its type expressions (entry 5) create it at any capability, `mut` included.

Sound: the object reaches nothing through captures, so its reachable object graph is empty and
a `mut` and an `imm` reference to it cannot observe any difference. `Gamma.filterFTV`.

## 7. Restrictions

Not in the paper; each only rejects programs.
- The self name of a literal, when written, is used in its bodies (`selfNameDeadCode`).
- A literal implementing `base.BaseId` declares only `#`, whose body is its parameter `x` or
  `x.as{..}` on a `base.BaseContainer` parameter (`baseIdBadBody`).

## 8. The type of a call

Paper: `call-t` types a call with any signature of `multiMeth` whose receiver and arguments
fit; `subs-t` then widens it.

`CallTyping` computes every signature whose receiver and arguments fit, keeps those whose result
meets the requirement and types the call with the first of their minimal results. This is one
of the types `call-t` derives. Two candidate results are never equivalent (asserted); two
minimal ones are a bare `X` and an `rc X`, both sound (`TypeSystemBugs.md` entry 1).
