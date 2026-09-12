# Type system bugs

One entry per bug in the type system itself. Each gives the rule as implemented, before
and after, minimized to pseudocode, so this file can be diffed against the formalism:
was the formalism wrong too, or did the implementation deviate?

Notation. `D` maps a type variable to its capability bound. `rcs(D,T)` is the set of
capabilities `T` can have: `{rc}` for `rc C[..]` and for `rc X`, all of `D(X)` for a bare
`X`. `T[rc]` replaces the outermost capability of `T`.

## Open

Not fixed; recorded so the next attempt starts from the mechanism.

- A call on the self name of a nested literal with no `[rc]` reaches the type system as
  `imm`, whatever the receiver. `InjectionSteps.nextMStarOp` declares `self : rc Fresh`
  with the literal's own not-yet-committed name; `methodHeaderAnd` finds no declaration for
  `Fresh`, so the `ICall` keeps an unknown type; the literal cannot commit while a body
  has unknowns (`commitToTable`, `hasU`), so no later pass resolves it either;
  `ToCore.callFromICall` finally stamps `imm`. Top-level declarations do not suffer:
  `stepDecM` types `this` against the declared name, in the table from the start.
  Explicit `[rc]` sidesteps it. `TypeSystemTest.implicitRcNotInferredInNestedLiteral`
  pins the current message, which names the assumption.
- Argument errors ("Type required by each promotion" in
  `methodArgumentCannotMeetAnyPromotion`) list the hygienic promotions also when nothing
  in the program is hygienic. The receiver error trims them because its list is display
  only; the argument list drives the argument matrix, and a hygienic argument against a
  non-hygienic signature is legitimate (`Allow mutH argument i`), so it can only be
  trimmed at display time, once the argument types are known.

## 1. The minimal type of a call is not unique

Frontend#27, 2026-08-24. Crash, not unsoundness. `PromotionMatrixTest`.

A call has a set of applicable promotions, each giving a result type; the type of the
call is the least of them.

    minimal(D, Ts) = { T in Ts | no T' in Ts with T' != T and T' <: T }

    was:  best(D, Ts) = the unique element of minimal(D, Ts), error if not unique
    now:  best(D, Ts) = the first element of minimal(D, Ts)
          -- promotions are generated in a fixed order, "as declared" first

Witness. `D(X) = {imm,mut}` and `Ts = {X, imm X}`, reached with an `imm` or `iso`
receiver, which is what keeps both "as declared" and "strengthen result" applicable.
`X <: imm X` fails because `mut` is not `<: imm`, and `imm X <: X` fails because `imm` is
not `<: mut`, so `minimal` has two elements. Both are sound, so `<:` cannot break the
tie. Taking the glb of the bound instead would make it unique but is unsound: it would
call an existing `imm` object `iso`.

## 2. Subtyping ignores the capability of a generic argument

Frontend#38 with StandardLibrary#49, 2026-09-08. Unsound. `GenericCapabilityAliasTest`.

    T1 <: T2  iff  T1 = T2  or  readImmVar(D,T1,T2)
                   or sameShape(D,T1,T2)  or  viaSuper(D,T1,T2)

    sameShape(D, T1, T2) =
      eqModVar(D, T1[mut], T2[mut])            -- outermost capability neutralised
      and forall r1 in rcs(D,T1), r2 in rcs(D,T2). r1 <: r2

    eqModVar(D, A, B) = match (A, B) with
      A = B                           -> true
      (X, rc X) or (rc X, X)          -> D(X) = {rc}
      (rc1 C[A1..An], rc2 C'[B1..Bn]) -> C = C'
                                         and forall i. eqModVar(D, Ai, Bi)
                                         was: rc1 and rc2 discarded here
                                         now: and rc1 = rc2
      otherwise                       -> false

`eqModVar` is entered at depth 0 with both capabilities already replaced by `mut`, so the
added conjunct constrains only depth 1 and below: the arguments become invariant.

Witness. `mut Box[mut C] <: mut Box[imm C]` held, and so did its converse, so a `mut`
alias stayed observable through an `imm` one.

Side condition dropped with it: a `BaseId` body must be `x` or `x.as{..}`, and the check
additionally demanded that the `.as` call resolve at an `imm` receiver. `BaseContainer` is
sealed and declares one `.as`, so the capability it resolves at says nothing about whether
the body is the identity.

## 3. A type used directly as an expression skipped its own bound check

Frontend#40, 2026-09-09. Unsound. `TypeSystemTest.typeNotWellKinded_typeExpressionViolatesBounds`.

Every fresh generic instantiation must satisfy the bound its parameters declare:

    kindOk(D, rc C[T1..Tn]) =
      let D_C = the bound C declares for each of its own parameters X1..Xn
      forall i. rcs(D,Ti) subsetOf D_C(Xi)  and  kindOk(D,Ti)

This is required at every site that instantiates a generic type: a supertype list, a
method signature, an explicit call type argument, a literal's own self type. A type used
directly as an expression - surface syntax like `C[T1..Tn].m(..)`, naming the type rather
than an instance of it - is a fifth such site and was the only one never checked.

    was:  checkType(D, rc C[T1..Tn]) = ok, no kindOk on C[T1..Tn] at all
    now:  checkType(D, rc C[T1..Tn]) = require kindOk(D, rc C[T1..Tn]), then as before

Witness. `Thaw[X:imm]:{ .apply(x:imm X):X -> x; }` bounds `X` to `{imm}`. `Thaw[mut
Cell].apply(cell)` instantiated `X` with `mut Cell`, outside that bound, unchecked.
`.apply`'s parameter type is `imm X`, viewpoint-adapted, so it accepted the argument
`cell:imm Cell` regardless of what `X` was; its return type is bare `X`, so the call's
result type became `mut Cell`. A `.set(..)` requiring a `mut` receiver then typechecked
against a reference declared, and never known to be more than, `imm`.

## 4. The self binding of an iso literal is discarded as a capture

Frontend#48, 2026-09-12. Rejects valid programs, not unsoundness.
`TypeSystemTest.isoLiteralCanUseItsSelfName`.

A literal's methods see the enclosing bindings through two steps: what the literal can
capture, decided by the literal's capability, and how a method sees what it captured,
decided by the method's capability. The self binding is not a capture: it is the object
under construction.

    discard(D, rc0, T) = rcs(D,T) not subsetOf {iso,imm,mut,read}
                         or (rc0 in {iso,imm} and rcs(D,T) not subsetOf {iso,imm})
    keep(D, rc0, G) = { x:T in G | not discard(D, rc0, T) }

    adapt(D, rc, T) = T[imm]       if rc = imm or rcs(D,T) subsetOf {iso,imm}
                      T[read]      if rc = read and T is mut _ or read _
                      readImm X    if rc = read and T is X or readImm X
                      T            if rc = mut and rcs(D,T) subsetOf {imm,mut,read}
                      T[read]      if rc = mut otherwise

    was:  G' = G, self : isoToMut(rc0) C[..]
          forall m. check m under adapt(D, rcOf(m), keep(D, rc0, G'))
          -- and the imm case of adapt additionally required rc0 in {mut,read}
    now:  G' = keep(D, rc0, G), self : isoToMut(rc0) C[..]
          forall m. check m under adapt(D, rcOf(m), G')

Witness. `iso Counter{'self mut .inc: mut Counter -> self }`: `self : mut Counter` is not
`iso`/`imm`, so `discard` dropped it for the `iso` literal and every use of `self` was
rejected as an illegal capture. Only `iso` shows it: for a `mut`/`read`/`imm` literal
`self` never meets the drop condition. The literal's capability now only decides what is
kept; the method's capability alone decides how it is seen. The dropped `rc0` guard on the
`imm` case was redundant: after `keep` everything an `iso`/`imm` literal holds is
`iso`/`imm` and is strengthened to `imm` by the first case anyway.
