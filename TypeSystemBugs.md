# Type system bugs

One entry per bug in the type system itself. Each gives the rule as implemented, before
and after, minimized to pseudocode, so this file can be diffed against the formalism:
was the formalism wrong too, or did the implementation deviate? The intended differences from
the formalism are in `PaperDifferences.md`.

Notation. `D` maps a type variable to its capability bound. `rcs(D,T)` is the set of
capabilities `T` can have: `{rc}` for `rc C[..]` and for `rc X`, all of `D(X)` for a bare
`X`. `T[rc]` replaces the outermost capability of `T`.

## Open

Not fixed; recorded so the next attempt starts from the mechanism.

- A call on the self name of a nested literal with no `[rc]` reaches the type system as
  `imm`, whatever the receiver. `InjectionSteps.nextMStarOp` declares `self : rc Fresh`
  (`rc` as seen from the method, bug 11) with the literal's own not-yet-committed name; `methodHeaderAnd` finds no declaration for
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
      (A, B) spellings of one X       -> as in entry 15
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
`iso`/`imm` and is strengthened to `imm` by the first case anyway. The formalism's `Lit-ok`
has the same two steps: `G|_{XBs,R}` before adding the self binding, then `G'[XBs,rcOf(M)]`.

## 5. A named declaration inside a method body could use the enclosing type parameters

Frontend#54, 2026-09-13. Crash, not unsoundness.
`DeclarationWellFormednessTest.inlineDeclarationImplementingAnEnclosingGenericWithoutFunnelling`.

A declaration is closed: every type variable it mentions is one of its own parameters.
The parameters of a declaration written inside a method body must themselves be in scope
there (funnelling), and the same name cannot be declared twice along the nesting.

    freeX(D[Xs]: Ts { Ms }) = (freeX(Ts) freeX(Ms)) \ Xs        -- must be empty
    inScope(D[Xs]: _ { _ } inside a scope Xs') = Xs subsetOf Xs'

    was:  parsing D[Xs]: _ { _ } inside a scope Xs' checks Xs subsetOf Xs'
          and then parses the body under Xs' itself, so any X in Xs' \ Xs
          survives as a free variable of D
    now:  the body is parsed under Xs alone; the names in Xs' \ Xs stay
          declared (so they cannot be redeclared) but a use of one is an error

Witness. `BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[Z]{} }`: `Z` reached the
type system in the supertype of `BreakInner`, whose own `bs` is empty, and `Kinding.ofX`
looked it up with `RC.get(bs,"Z")`, which is offensive: `OneOr.OneOrException` instead of
a message. The same happened with `Z` in one of the declaration's own signatures, and `mut
Z` passed kinding altogether because `checkRCX` never consults `bs`. The formalism has the
rule (B2 in the appendix, `X in dom(XBs)` for every type in `Lit-ok`), the implementation
only had the captured-parameter half of it (`Gamma.filterFTV`, "uses type parameters that
are not propagated"), which sees a parameter whose type mentions the free variable but
never a mention written inside the declaration itself.

## 6. Two spellings of one signature in a method table

Frontend#89, 2026-09-28. Crash, not unsoundness.
`TypeSystemTest.inheritedMethodSpelledWithAndWithoutRedundantRcOnTypeVariable`.

Under `D(X) = {rc}` the types `X` and `rc X` are the same type, and the type system compares
types with `eqModVar` (bug 2) for that reason. A type variable with no bound is `X:imm`.
Inference spells a variable `rc X` at every position whose declared bound is `{rc}`
(`InjectionSteps.normToBounds`), so a literal's supertype list, fixed when the literal is
first expanded from the head as then guessed, and its inherited methods, re-instantiated
from the head after normalization, can spell the same signature in the two ways.

    sameSig(D, s1, s2) = same name, capability, bounds, origin, abstractness
                         and forall i. eqModVar(D, s1.ts[i], s2.ts[i])
                         and eqModVar(D, s1.ret, s2.ret)

    mostSpecificByOrigin(D, sources, chosen) =
      forall s in sources with not sameSig(D, s, chosen). origin(s) != origin(chosen)
      was: with s != chosen (structural equality)

Witness. `M[R:**]:{ mut .a: R; mut .b: R -> this.a; }`, `TM[K]:{ read #(x: K): mut M[K] }`,
`MM:{ #[K]: TM[K] -> {x -> { .a -> x }} }`. The inner literal reaches the type system as
`iso _AMM[K:imm]: M[K]{ mut .a: imm K -> x; mut .b: imm K }`: the supertype comes from
`TM[K]`, still spelled as written, the methods from `TM[imm K]`, the normalized head of the
outer literal. `M[K]` yields `mut .b: K@M` and the table holds `mut .b: imm K@M`; the two
are not structurally equal and share an origin, which the assert takes for the same generic
supertype inherited twice with different instantiations. Any single-capability bound shows
it (`K:mut` gives `K` against `mut K`), `K:*` does not, and writing `imm K` in either `TM`
or `MM` makes the two spellings agree.

## 7. A decided type argument of a call is re-inferred from the arguments

Frontend#89, 2026-09-28. Rejects valid programs, not unsoundness.
`TypeSystemTest.lambdaParameterTypedFromExplicitTypeArgumentOfReceiverCall`,
`explicitTypeArgumentKeepsItsRcAgainstTheArgument`.

The type arguments of a call are the receiver's own type arguments followed by the method's:
those written explicitly are decided, the others are inferred from the arguments and from
the expected result. A decided type argument is never re-decided; `nextMStarOp` already
follows this for literals (`keepDecided`), the call rule did not.

    decided(T) = T has no unknown and, if T = rc C[..], rc is known
    base = receiver type arguments ++ explicit type arguments (unknown where not written)
    targs[i] = base[i]                                     if decided(base[i])
               meet(base[i], fromArgs[i].., fromResult[i]) otherwise
    was: targs[i] = meet(base[i], fromArgs[i].., fromResult[i]) always

`meet` on two heads prefers the subtype (`leastBad`) and on one head with two capabilities
answers `imm` (`meetRcNoH`), so an argument more specific than the explicit type argument
replaced it. The arguments were already protected: `requiredOnArgs` pushes `base` down
before an argument body is inferred. The result type of the call was not, and the type
system re-derives every call, so the wrong result surfaced only through a literal typed from
it, whose head is stamped by inference.

Witness. `Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }`,
`Fls:{ #[R:*](r: R): mut Fl[R]; }`, `L[E:*]:TF[E]{ }`, and
`fls#[read TF[E]](xs).g[E]{c -> c}` with `xs: mut L[E]`. `R` of `#` became `mut L[E]`, the
receiver of `.g` `mut Fl[mut L[E]]`, the lambda `Fn[mut L[E], read TF[E]]`, rejected against
`Fn[read TF[E], read TF[E]]`; with `xs: mut TF[E]` the head stayed and `R` became
`imm TF[E]`. The same `.g[E]{c -> c}` on a parameter of type `mut Fl[read TF[E]]` compiled,
and so did the lambda passed directly to a call with explicit type arguments, since only the
result was re-decided. Receivers of a known type now keep their declared spelling in the
inferred output (`F[_HR,T,_HR]` rather than `F[imm _HR,imm T,_HR]` under `imm` bounds).

## 9. Inference decided on the hygienic capability of an expected type

Frontend#94, 2026-09-29; Frontend#110, 2026-09-30. Rejects valid programs, not unsoundness.
`CapabilityTypingTest.readHEmptyLiteralLeavesMutAbstract`,
`readHEmptyLiteralArgumentLeavesMutAbstract`, `readHLiteralWithBodyLeavesMutAbstract`,
`readHLambdaArgumentLeavesMutOverloadAbstract`, `readHLambdaResultLeavesMutOverloadAbstract`,
`mutHLambdaArgumentImplementsBothOverloads`,
`mutHEmptyLiteralMustImplementMut`, `mutHResultDoesNotFlowToMutFromReadReceiver`.

Inference only produces what would be accepted if written by hand. The capability of a
literal or a type expression is never `readH` or `mutH` (A7), and the parser enforces it.
A literal takes its capability `rc` from the expected type and is committed with `noH(rc)`
(`InjectionSteps.commitToTable`); every choice inference makes on that capability must be
made on `noH(rc)` too. Two places used `rc`:
- a fresh object `{}` with no method bodies becomes a type expression (`justAType`);
- a method written without a capability is copied into the overloads it matches, and the
  `mut` copy is dropped when the literal can never be `mut` (`Methods.pairWithSig`).

    was:  justAType: E.Type(rc C[..])       with rc the capability of the expected type
    now:  justAType: E.Type(noH(rc) C[..])  as for a literal with bodies
    was:  drop the mut overload iff isReadOrImm(rc)
    now:  drop the mut overload iff isReadOrImm(noH(rc))
          noH(readH) = read, noH(mutH) = mut

`core.E.Type`, `core.E.Literal` and `core.Sig` assert the capabilities the parser allows,
so an inferred form that could not be written fails at construction.

Witness. `B:{ mut .m: B }`, `A:{ .b: readH B -> {} }` became the type expression `readH B`;
`callable(readH, mut)` holds, so the abstract `mut .m` was required, while `read B -> {}`
was accepted. A `mutH` expected type gave `mutH B`, printed in inferred contexts as
`.b:mutH B->mutH B`, a body that does not parse.
`Box:{ mut .get: A; read .get: A; }`, `Need:{ #(b: readH Box): A -> A }`,
`User:{ read .a: A -> A; read .f: A -> Need#{ .get -> this.a }; }` kept the `mut` copy of
`.get`, and the committed `read` literal was rejected as dead code; with `read Box` in
`Need` it was accepted.

## 11. Inference sees the self name of a nested literal with the literal's capability

Frontend#96, 2026-09-29. Rejects valid programs, not unsoundness.
`TypeSystemTest.nestedSelfDispatchUsesMethodCapability`,
`nestedSelfDispatchUsesReadMethodCapability`, `nestedSelfCapturedDeeperUsesMethodCapability`,
`isoNestedSelfCapturedDeeperIsMut`.

The type system gives the self name `isoToMut(rc0) C[..]` and adapts it by the method's
capability like every other binding the method sees (`adapt` of bug 4). Inference chooses
the overload of a call without `[rc]` from the capability of its receiver, so it must see
the self name the same way.

    self seen by m, in the type system = adapt(D, rcOf(m), isoToMut(rc0) C[..])
                                       = imm C[..]           if rcOf(m) = imm or rc0 = imm
                                         read C[..]          if rcOf(m) = read
                                         isoToMut(rc0) C[..] if rcOf(m) = mut
    was:  inference declares self : rc0 C[..] inside the scope of m, and Gamma.getWithRC
          adapts a binding only by the scopes strictly inside its declaration
    now:  inference declares self : isoToMut(rc0) C[..] in a scope of its own around the scope
          of m, so Gamma.getWithRC adapts it by m and every deeper scope, like a capture

Top-level declarations did not suffer: `stepDecM` types `this` with `rcOf(m)` directly,
which is the adapted type: a top-level declaration has `rc0 = mut`.
Four observable shapes, one per test: `self.m1` in an `imm` method of a `mut` literal
dispatched to `mut .m1`; the same in a `read` method; `self` captured by a literal nested
inside an `imm` method stayed `mut` there, since the deeper scope is `mut` and the `imm`
scope of the method is the declaration scope itself; and for an `iso` literal, `self`
captured by a nested literal became `imm` (`getWithRC` treats a captured `iso` binding as
`imm`) where the type system has `mut`. In each case the type system rejected the call
inference had annotated (`receiverRCBlocksCall`).

Witness. `A:{ imm .m1: A; mut .m1: mut A; .m2: A }`,
`User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> self.m1 } }`: inference produced
`self.m1[mut]` in the `imm` method `.m2`; the top-level `B:A{ .m1 -> this; .m2 -> this.m1 }`
was accepted.

## 12. A promotion of a `read/imm X` resolves `read/imm` before the promotion

Frontend#98, 2026-09-29. Unsound. `CapabilityTypingTest.genericReadHBoxReadImmGetIsNotRead`,
`genericReadHBoxReadImmGetOfReadHIsNotRead`, `genericReadHSinkAcceptsReadHReadImmArgument`.

A promotion maps each capability of a method type through a mode `prom` (`strong`, `flexy`,
`hyg`, `useRead`). A type variable takes the mode through its bound; `read/imm X` stands for
`readImm(rc) C` at the instantiation `X = rc C`, so the mode applies to `readImm(rc)`.
`readImm` sends every capability outside `{iso,imm}` to `read`, hygienic ones included.

    prom^f(D, readImm X) = readImm X      if forall r in R. prom(r) = r
                           f(prom(R)) X   otherwise
      now:  R = { readImm(rc) | rc in D(X) }
      was:  prom(R) above was { readImm(prom(rc)) | rc in D(X) }
            and the unchanged test was forall rc in D(X). readImm(prom(rc)) = rc

Witness. `Box[X:*]:{ mut .get: X; read .get: read/imm X }` and
`#[Y:mut](r: readH Box[Y]): read Y -> r.get`, through "Allow readH arguments": `hyg(mut) =
mutH`, `readImm(mutH) = read`, so the call had type `read Y`, capturable by an object
literal, where the concrete `readH Box[mut Foo]` gives `hyg(readImm(mut)) = readH Foo`.
Under `D(Y) = {readH}` it gave `read Y` too; swapping the order without changing the
unchanged test would give `read/imm Y`, still `read`, since `hyg(readImm(readH)) = readH`:
the test must compare against `readImm(rc)`, not `rc`. On parameters the same order made
`useRead` require `imm Y` for `read/imm Y` with `D(Y) = {mut}` where the concrete call
requires `readH`, rejecting valid calls. The formalism defines `\prom^\f(\XBs,\readImm\,\X)`
and `\noChangeRI` as `now`.

The old order also gave one call two candidates with equivalent but different results. With
`D(X) = {iso,imm}`, `readImm(iso) = imm` failed the unchanged test, so every promotion of
`read/imm X` gave `imm X` next to the `read/imm X` "as declared": both denote only `imm`.
`minimal` (entry 1) drops `T` when some `T' != T` has `T' <: T`, so it assumes `<:` is
antisymmetric on the candidate results; the two removed each other and `best` crashed,
also with no requirement and in the error for an unmet one (Frontend#92,
`CapabilityTypingTest.readImmResultOfIsoImmBound*`). With the unchanged test on
`readImm(rc)`, a mode either keeps a variable type as written or gives an `RCX` not
equivalent to it, so candidate results are never equivalent; `CallTyping.bests` asserts it.

## 13. Inference leaves open the capability of a type argument

Frontend#128, 2026-10-01. Rejects valid programs, not unsoundness.
`CapabilityTypingTest.readArgumentToReadTypeVariableParameterInfersItsTypeArgument`,
`immArgumentToImmTypeVariableParameterInfersItsTypeArgument`,
`readResultOfReadTypeVariableInfersItsTypeArgument`,
`lambdaWithReadParameterInfersItsSupertypeTypeArgument`,
`isoArgumentToTypeVariableWithoutIsoBoundInfersItsTypeArgument`,
`readArgumentToReadTypeVariableWithoutImmBoundInfersItsTypeArgument`,
`lambdaWithReadParameterWithoutImmBoundInfersItsSupertypeTypeArgument`.

Inference only produces what would be accepted if written by hand (bug 9). A type argument
for `X` takes its capability from the types matched against the occurrences of `X`. Two
matches say nothing about that capability: `rc X` against `rc' C[..]`, since `rc` replaces
whatever `X` carries, and a bare `X` against `iso C[..]`, since `iso` is a subtype of every
capability. When every match on `X` is of these two kinds the capability is open, and it must
be closed inside `D(X)`. `?` is the unknown capability: `meet` drops it against any other,
and an inferred type still carrying it is emitted as `imm`.

    refine(rc X, rc' C[..]) = X := ? C[..]
      was:                    X := iso C[..]  -- iso standing for ?, since meet drops it too
    close(D(X), ? C[..])    = ? C[..]      if imm in D(X)
                              read C[..]   otherwise
    close(D(X), iso C[..])  = close(D(X), ? C[..])   if iso not in D(X)
      was: no close on call type arguments nor on literal supertype arguments;
           iso C[..] reached the output

`read` is the lowest capability that can still be captured.
`close` runs at every step of the fixpoint, so it may only commit to what `meet` still drops:
`read` is dropped against any capability but `iso`, and `read` accepts an `iso` argument
anyway; `imm` is not dropped (`meet(imm, mut) = imm`), so `?` stays open until the output.
Written type arguments are not affected: the output keeps them as written. With `?` no longer
spelled `iso`, the two special cases that recognised the placeholder by its `iso` go: in
`decidedThen` a literal argument giving `iso C[..]` for `X` is a constraint like any other
(one giving `? C[..]` is not decided, as for any unknown capability), and `keepDecided` keeps
a decided `iso C[..]` instead of replacing it with the capability found in the body.

Witness. `Util:{ .m[Y:*](y: read Y): Foo -> Foo }`, `A:{ .f(x: read Foo): Foo -> Util.m(x) }`
became `Util.m[imm,iso Foo](x)`, not well kinded, while `Util.m[Foo](x)` was accepted. The
same for `imm Y` with an `imm Foo` argument, for an expected `read Foo` against a result
`read Y`, for a lambda `{ #(y: read Foo): Foo -> Foo }` against `Cons[Y:*]:{ #(y: read Y): Foo }`
(`Cons[iso Foo]`), and for an argument `x: iso Foo` to a parameter `y: Y` under `Y:*`. Under
`Y:**` the `iso` was well kinded and became the result of `Y`; the unknown capability now gives
`imm` there too, while an `iso` argument under `Y:**` keeps `iso`.

## 14. Inference types a capture the type system drops for its type parameters

Frontend#129, 2026-10-01. Crash, not unsoundness.
`TypeSystemTest.drop_ftv_notPropagatedIntoExplicitFoo`,
`drop_ftv_typeVariableNotPropagatedIntoExplicitFoo`,
`drop_ftv_notPropagatedTypeReachesInferredTypeArgument`,
`drop_ftv_notPropagatedTypeReachesNestedLiteral`, `drop_ftv_notPropagatedIntoFooDeclaringOther`.

A literal written by name, `D[Xs]`, keeps only the bindings whose type mentions no type
variable outside `Xs` (`Gamma.filterFTV`, bug 5). Inference must not give such a binding a
type inside `D`: any type inferred from it mentions a type variable that is not in scope
there, which no one could write (the parser rejects it, `genericNotFunnelled`).

    keep(Xs, G) = { x:T in G | FTV(T) subsetOf Xs }     -- type system, per named literal

    x used inside the scopes s1..sn strictly inside the declaration of x
      -- Xs of an inferred-name literal is the whole enclosing scope
    was:  seen(x) = adapt over s1..sn, with the bound of a bare or read/imm X read from Xs(si)
    now:  error at the use if FTV(T) not subsetOf Xs(si) for some si, else as before

Witness. `User:{ read .m[X:*](x:X):read Foo -> read Foo:{ read .m:Bar -> x } }`: `adapt`
looked `X` up in the bounds of `Foo`, which are empty, and `RC.get` crashed. A type other than
a bare `X` was adapted by its capability alone, so with `beer:Beer[X]` inference typed it and
carried `X` further: `Id#beer` became `Id#[Beer[X]]`, and the type system, which checks the
type arguments of a call before its arguments, crashed in `Kinding` looking `X` up in the
bounds of `Foo`; `Do#{ beer.bar }` committed the nested literal with parameters `[X]` and
`checkLiteral` failed its assert that they are in scope. Now inference rejects the use, in the
words of `genericNotFunnelled`, so the type system never sees a dropped binding used: its own
error for that case is unreachable. `ToCore` asserts that every inferred type argument, type
expression and literal type parameter is in scope, where the scope of a named literal is its
own type parameters only.

## 15. Inherited signatures agree up to a fixed set of spellings, not up to type equality

Frontend#146, 2026-10-04. Rejects valid programs, not unsoundness.
`MethodCompositionTest.methodGenericSameReadImmViaExactBoundInherited`,
`classGenericSameReadImmViaExactBoundInherited`, `methodGenericSameReadViaExactBoundInherited`,
`methodGenericDifferingReadImmViaExactBoundInherited`.

A method inherited from several supertypes with no signature written takes, at each
parameter and at the result, the one type all the inherited signatures agree on
(`Methods.agreement`). They agree when they are the same type, and the type system decides
that with `eqModVar`, whose variable case covers every spelling of `X`:

    eqModVar(D, A, B) = ...
      (A, B) spellings of one X       -> |D(X)| = 1 and rcs(D,A) = rcs(D,B)
                                         -- spellings: X, rc X, readImm X
                                         -- rcs(D, readImm X) = { readImm(rc) | rc in D(X) }

    agree(D, T1..Tn) =
      was:  the one element of { norm(D,Ti) }, error if more than one
            norm(D, X) = rc X if D(X) = {rc};  norm(D, rc C[..]) maps norm on the arguments
            norm(D, T) = T otherwise                     -- readImm X never rewritten
      now:  T1 if forall i. eqModVar(D, T1, Ti), error otherwise

`norm` rewrote only a bare `X`, so `readImm X` stayed apart from both `X` and `rc X`: under
`D(T) = {imm}` the options `T` and `read/imm T` (both `imm`), and under `D(T) = {mut}` the
options `read T` and `read/imm T` (both `read`), were reported as differing in capability.
Under `D(T) = {mut}`, `T` and `read/imm T` still disagree: `mut` against `read`.

Witness. `Foo:{ .get[T:imm]: T }`, `Bar:{ .get[T:imm]: read/imm T }`, `A:Foo,Bar{}` was
rejected with "Different options are present in the implemented types: "T", "read/imm T".
They differ in reference capability", while `A:Foo,Bar{ .get[T:imm]: T }`, the same choice
written by hand, was accepted. The same with class type parameters,
`Foo[X:imm]:{ .get: X }`, `Bar[X:imm]:{ .get: read/imm X }`, `A[Y:imm]:Foo[Y],Bar[Y]{}`.