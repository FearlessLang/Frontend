package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class CapabilityTypingTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failParse(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 2 UnexpectedToken", input);
  }
  static final String box= """
Box:{ #[T:*](t: T): mut Box[T] -> { .get -> t; .rget -> t; .riget -> t } }
Box[T:*]:{ mut .get: T; read .rget: read T; read .riget: read/imm T }
""";

@Test void isoIsNotAMethodCapability(){failParse("""
001| A:{ iso .m1: iso A -> this }
   |     ^^^~~~~~~~~~~~--------

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Capability iso used.
Capabilities iso, readH and mutH are not allowed on method declarations.
Use one of read, mut, imm.
""",List.of("""
A:{ iso .m1: iso A -> this }
"""));}
@Test void callMutFromMutH(){ok(List.of("""
Void:{}
A:{ .b: mutH B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void mutHResultFlowsToMut(){ok(List.of("""
A:{ .b: mutH B -> {}; .doThing: mut B -> this.b }
B:{}
"""));}
@Test void mutHResultDoesNotFlowToMutFromReadReceiver(){fail("""
001| A:{ read .b: mutH B -> {}; read .doThing: mut B -> this.b }
   |                            ------------------------^^^^^^

While inspecting method call ".b" > ".doThing" line 1
The body of method ".doThing" of type declaration "A" is an expression returning "mutH B".
Method call "read A.b" has type "mutH B" instead of a subtype of "mut B".

See inferred typing context below for how type "mut B" was introduced: (compression indicated by `-`)
A:{read .b:mutH B->mutH B;read .doThing:mut B->this.b[read]}
""",List.of("""
A:{ read .b: mutH B -> {}; read .doThing: mut B -> this.b }
B:{}
"""));}
@Test void mutHResultFlowsToMutWithIsoArgument(){ok(List.of("""
A:{ .b(a: mut A): mutH B -> {}; .doThing: mut B -> this.b(iso A) }
B:{}
"""));}
@Test void mutHResultFlowsToMutWithFreshArgument(){ok(List.of("""
A:{ .b(a: mut A): mutH B -> {}; .doThing: mut B -> this.b({}) }
B:{}
"""));}
@Test void noCallMutFromImm(){fail("""
002| A:{ .b: imm B -> {}; .doThing: Void -> this.b.foo.ret }
   |                      ------------------~~~~~~^^^^^---

While inspecting ".doThing" line 2
This call to method "mut B.foo" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.b.foo[mut]
""",List.of("""
Void:{}
A:{ .b: imm B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void noCallMutFromReadH(){fail("""
002| A:{ .b: readH B -> {}; .doThing: Void -> this.b.foo.ret }
   |                        ------------------~~~~~~^^^^^---

While inspecting ".doThing" line 2
This call to method "mut B.foo" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.b.foo[mut]
""",List.of("""
Void:{}
A:{ .b: readH B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void noCallMutFromRead(){fail("""
002| A:{ .b: read B -> {}; .doThing: Void -> this.b.foo.ret }
   |                       ------------------~~~~~~^^^^^---

While inspecting ".doThing" line 2
This call to method "mut B.foo" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.b.foo[mut]
""",List.of("""
Void:{}
A:{ .b: read B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void readThisIsReadH(){ok(List.of("""
A:{ read .self: readH A -> this }
"""));}
@Test void noCaptureOfReadHInMutLiteral(){fail("""
002| B:{ .break(prisoner: readH B): mut A[readH B] -> {prisoner} }
   |     ----------------------------------------------^^^^^^^^^

While inspecting parameter "prisoner" > ".prison" line 2 > ".break(_)" line 2
parameter "prisoner" has type "readH B".
The type of parameter "prisoner" is hygienic (readH or mutH)
and thus it cannot be captured in the object literal instance of "mut A[readH B]" (line 2).

Compressed relevant code with inferred types: (compression indicated by `-`)
prisoner
""",List.of("""
A[X:imm,mut,read,readH]:{ mut .prison: X }
B:{ .break(prisoner: readH B): mut A[readH B] -> {prisoner} }
"""));}
@Test void noCaptureOfHygienicTypeVariableInMutLiteral(){fail("""
002| B[X:mut,imm,read,mutH,readH]:{ .break(x: X): mut A[X] -> { x } }
   |                                ----------------------------^--

While inspecting parameter "x" > ".prison" line 2 > ".break(_)" line 2
parameter "x" has type "X".
The type of parameter "x" can be instantiated with hygienics (readH or mutH)
and thus it cannot be captured in the object literal instance of "mut A[X]" (line 2).

Compressed relevant code with inferred types: (compression indicated by `-`)
x
""",List.of("""
A[X:mut,imm,read,mutH,readH]:{ mut .prison: X }
B[X:mut,imm,read,mutH,readH]:{ .break(x: X): mut A[X] -> { x } }
"""));}
@Test void noReadImmEscapeFromIsoReceiver(){fail("""
004| C:{ #: mutH B -> A.m(B).absMeth }
   |     -------------^^^^^^^^^^^^^^

While inspecting method call ".absMeth" > "#" line 4
The body of method "#" of type declaration "C" is an expression returning "B".
Method call "read L[_].absMeth" has type "B" instead of a subtype of "mutH B".

See inferred typing context below for how type "mutH B" was introduced: (compression indicated by `-`)
C:{#:mutH B->A.m[read](B).absMeth[read]}
""",List.of("""
B:{}
L[X:*]:{ read .absMeth: read/imm X }
A:{ read .m(par: imm B) : mutH L[imm B] -> mut L[imm B]{.absMeth->par} }
C:{ #: mutH B -> A.m(B).absMeth }
"""));}
@Test void immCapturedAsReadH(){ok(List.of("""
B:{}
L[X:*]:{ imm .absMeth: readH X }
A:{ read .m[T:*](par: imm T) : readH L[imm T] -> read L[imm T]{.absMeth->par} }
"""));}
@Test void mutCapturedInMutLiteral(){ok(List.of("""
B:{}
L[X:*]:{ imm .absMeth: imm X }
A:{ read .m[T:*](par: mut T) : mut L[mut T] -> mut L[mut T]{.absMeth->par} }
"""));}
@Test void noCaptureAsMutHInMutLiteral(){fail("""
003| A:{ read .m[T:mut,imm,read,readH,mutH](par: T) : read L[mutH T] -> mut L[mutH T]{.absMeth->par} }
   |     -----------------------------------------------------------------------------~~~~~~~~~~^^^^

While inspecting parameter "par" > ".absMeth" line 3 > ".m(_)" line 3
parameter "par" has type "T".
The type of parameter "par" can be instantiated with hygienics (readH or mutH)
and thus it cannot be captured in the object literal instance of "mut L[mutH T]" (line 3).

Compressed relevant code with inferred types: (compression indicated by `-`)
par
""",List.of("""
B:{}
L[X:mut,imm,read,readH,mutH]:{ mut .absMeth: imm X }
A:{ read .m[T:mut,imm,read,readH,mutH](par: T) : read L[mutH T] -> mut L[mutH T]{.absMeth->par} }
"""));}
@Test void noMutCaptureInIsoLiteral(){fail("""
003| A:{ read .m(par: mut B) : iso L -> iso L{.absMeth->par} }
   |     -------------------------------------~~~~~~~~~~^^^^

While inspecting parameter "par" > ".absMeth" line 3 > ".m(_)" line 3
parameter "par" has type "mut B".
parameter "par" can observe mutation; thus it cannot be captured in the "iso" object literal instance of "iso L" (line 3).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
par
""",List.of("""
B:{}
L:{ mut .absMeth: mut B }
A:{ read .m(par: mut B) : iso L -> iso L{.absMeth->par} }
"""));}
@Test void noReadCaptureInImmLiteral(){fail("""
003| A:{ read .m(par: read B) : imm L -> imm L{.absMeth->par} }
   |     --------------------------------------~~~~~~~~~~^^^^

While inspecting parameter "par" > ".absMeth" line 3 > ".m(_)" line 3
parameter "par" has type "read B".
parameter "par" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "L" (line 3).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
par
""",List.of("""
B:{}
L:{ imm .absMeth: read B }
A:{ read .m(par: read B) : imm L -> imm L{.absMeth->par} }
"""));}
@Test void isoLiteralCannotCaptureMut(){fail("""
002| Foos:{ #(a: mut A): iso Foo -> iso Foo{a} }
   |        --------------------------------^^

While inspecting parameter "a" > "#" line 2 > "#(_)" line 2
parameter "a" has type "mut A".
parameter "a" can observe mutation; thus it cannot be captured in the "iso" object literal instance of "iso Foo" (line 2).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
a
""",List.of("""
A:{}
Foos:{ #(a: mut A): iso Foo -> iso Foo{a} }
Foo:{ mut #: mut A }
"""));}
@Test void minimalMatcher(){ok(List.of("""
Matcher[R:*]:{ mut .get: R }
PreR:{ mut .get: mut MyRes -> {} }
MyRes:{}
MatcherContainer:{ read .match[R:*](m: mut Matcher[R]): R -> m.get }
Usage:{
  .direct(preR: mut PreR): mut MyRes -> MatcherContainer.match{ preR.get };
  .indirect(r: mut MyRes): mut MyRes -> MatcherContainer.match{ r };
  }
"""));}
@Test void isoPromotionWithASingleMutArgument(){ok(List.of("""
A:{ mut .a(a: iso A): iso A -> B.foo(a).a1 }
B:{ .foo(a: iso A): iso Container -> ContainerF#(a) }
ContainerF:{ #(a: mut A): mut Container -> { .a1 -> a; .a2 -> a } }
Container:{ mut .a1: mut A; mut .a2: mut A }
"""));}
@Test void noIsoPromotionWithMutAndMutHArguments(){fail("""
002| B:{ .foo(a: mut A, aa: mutH A): iso A -> a }
   |     -------------------------------------^

While inspecting parameter "a" > ".foo(_,_)" line 2
The body of method ".foo(_,_)" of type declaration "B" is an expression returning "mut A".
Parameter "a" has type "mut A" instead of a subtype of "iso A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
B:{.foo(a:mut A,aa:mutH A):iso A->a}
""",List.of("""
A:{ mut .a: iso A -> B.foo(this, this) }
B:{ .foo(a: mut A, aa: mutH A): iso A -> a }
"""));}
@Test void noIsoPromotionWithTwoMutArguments(){fail("""
002| B:{ .foo(a: mut A, aa: mut A): iso A -> a }
   |     ------------------------------------^

While inspecting parameter "a" > ".foo(_,_)" line 2
The body of method ".foo(_,_)" of type declaration "B" is an expression returning "mut A".
Parameter "a" has type "mut A" instead of a subtype of "iso A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
B:{.foo(a:mut A,aa:mut A):iso A->a}
""",List.of("""
A:{ mut .a: iso A -> B.foo(this, this) }
B:{ .foo(a: mut A, aa: mut A): iso A -> a }
"""));}
@Test void noIsoPromotionWhenThisIsAlsoShared(){fail("""
002| B:{ .foo(a: mut A): iso A -> a }
   |     -------------------------^

While inspecting parameter "a" > ".foo(_)" line 2
The body of method ".foo(_)" of type declaration "B" is an expression returning "mut A".
Parameter "a" has type "mut A" instead of a subtype of "iso A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
B:{.foo(a:mut A):iso A->a}
""",List.of("""
A:{ mut .a(randomSharedMut: mut A): iso A -> B.foo(this) }
B:{ .foo(a: mut A): iso A -> a }
"""));}
@Test void promoteOneMutHToMutAndBack(){ok(List.of("""
Void:{} Name:{}
Person:{ mut .name: mut Ref[Name] }
Usage:{ .mutate(p: mutH Person): mutH Ref[Name] -> p.name }
Ref[X:*]:{ read .get: read/imm X; mut .set(x: X): Void }
"""));}
@Test void noPromotionOfOneMutHToIso(){fail("""
003| Usage:{ .mutate(p: mutH Person): iso Ref[Name] -> p.name }
   |         ------------------------------------------^^^^^^

While inspecting method call ".name" > ".mutate(_)" line 3
The body of method ".mutate(_)" of type declaration "Usage" is an expression returning "mutH Ref[Name]".
Method call "mut Person.name" has type "mutH Ref[Name]" instead of a subtype of "iso Ref[Name]".

See inferred typing context below for how type "iso Ref[Name]" was introduced: (compression indicated by `-`)
Usage:{.mutate(p:mutH Person):iso Ref[Name]->p.name[mut]}
""",List.of("""
Void:{} Name:{}
Person:{ mut .name: mut Ref[Name] }
Usage:{ .mutate(p: mutH Person): iso Ref[Name] -> p.name }
Ref[X:*]:{ read .get: read/imm X; mut .set(x: X): Void }
"""));}
@Test void isoUsedOnceIsFine(){ok(List.of("""
Caps:{} Void:{}
A:{ .notBreak(x1: iso Caps, x2: iso Caps): Void -> this.notBreak(x1, x2) }
"""));}
@Test void isoUsedTwiceDirectly(){fail("""
002| A:{ .break(x1: iso Caps, x2: iso Caps): Void -> this.break(x1, x1) }
   |     -------------------------------------------------------^^^~~~~

While inspecting ".break(_,_)" line 2
Iso parameter "x1" violates the single-use rule in method "A.break(_,_)" (line 2).
It is used directly 2 times.
Iso parameters can be used directly at most once.
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.break(x1,x1)
""",List.of("""
Caps:{} Void:{}
A:{ .break(x1: iso Caps, x2: iso Caps): Void -> this.break(x1, x1) }
"""));}
@Test void isoUsedDirectlyAndCaptured(){fail("""
003|   .break(x1: iso Caps, x2: iso Caps): Void -> this.breakTwo(x1, B{ x1 });
   |   ----------------------------------------------------------^^^~~~~~~---

While inspecting ".break(_,_)" line 3
Iso parameter "x1" violates the single-use rule in method "A.break(_,_)" (line 3).
It is used directly and also captured into object literals.
An iso parameter must be either captured, or used directly once (but not both).
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.breakTwo(x1,B{.x:Caps->x1})
""",List.of("""
Caps:{} Void:{}
A:{
  .break(x1: iso Caps, x2: iso Caps): Void -> this.breakTwo(x1, B{ x1 });
  .breakTwo(x1: iso Caps, b: B): Void -> {};
  }
B:{ .x: Caps }
"""));}
@Test void twoDistinctIsosOneUsedOneCaptured(){ok(List.of("""
Caps:{} Void:{}
A:{
  .break(x1: iso Caps, x2: iso Caps): Void -> this.breakTwo(x1, B{ x2 });
  .breakTwo(x1: iso Caps, b: B): Void -> {};
  }
B:{ .x: Caps }
"""));}
@Test void isoCanBeCapturedMultipleTimesAsImm(){ok(List.of("""
A:{ #(a: iso A): B -> Block#(B{a}, B{a}) }
B:{ #: A }
Block:{ #[X1:*,R:*](a1: X1, a2: R): R -> a2 }
"""));}
@Test void immBoundedTypeVariableCanBeCapturedMultipleTimes(){ok(List.of("""
A:{ #[X:imm](a: X): B[X] -> Block#(B[X]{a}, B[X]{a}) }
B[X:imm]:{ #: imm X }
Block:{ #[X1:imm, R:imm](a1: X1, a2: R): R -> a2 }
"""));}
@Test void isoBoundedTypeVariableCanBeCapturedMultipleTimesAsImm(){ok(List.of("""
A:{ #[X:iso](a: X): B[X] -> Block#(iso B[X]{a}, iso B[X]{a}) }
B[X:iso]:{ #: imm X }
Block:{ #[X1:iso, R:iso](a1: X1, a2: R): R -> a2 }
"""));}
@Test void readHBoxGetIsReadH(){ok(List.of("""
Foo:{}
Box[X:*]:{ mut .get: X; read .get: read X }
Test:{ #(r: readH Box[Foo]): readH Foo -> r.get }
"""));}
@Test void readHBoxGetIsNotImm(){fail("""
003| Test:{ #(r: readH Box[Foo]): Foo -> r.get }
   |        -----------------------------^^^^^

While inspecting method call ".get" > "#(_)" line 3
The body of method "#(_)" of type declaration "Test" is an expression returning "readH Foo".
Method call "read Box[_].get" has type "readH Foo" instead of a subtype of "Foo".

See inferred typing context below for how type "Foo" was introduced: (compression indicated by `-`)
Test:{#(r:readH Box[Foo]):Foo->r.get[read]}
""",List.of("""
Foo:{}
Box[X:*]:{ mut .get: X; read .get: read X }
Test:{ #(r: readH Box[Foo]): Foo -> r.get }
"""));}
@Test void readHBoxReadImmGetIsImm(){ok(List.of("""
Foo:{}
Box[X:*]:{ mut .get: X; read .get: read/imm X }
Test:{ #(r: readH Box[Foo]): Foo -> r.get }
"""));}
@Test void readBoxGetPromotesToReadH(){ok(List.of("""
Foo:{}
Box[X:*]:{ mut .get: X; read .get: read X }
Test:{ #(r: read Box[Foo]): readH Foo -> r.get }
"""));}
@Test void readHChainKeepsReadH(){ok(List.of("""
Foo:{}
Box[X:*]:{ mut .get: X; read .get: read X }
MutyBox:{ mut .mb: mut Box[Foo]; read .rb: read Box[Foo] }
Test1:{ #(r: readH MutyBox): readH Foo -> r.rb.get }
Test2:{ #(r: read MutyBox): read Foo -> r.rb.get }
"""));}
@Test void dispatchOnASingleCandidate(){ok(List.of("""
A:{ .m1: A; .m2: A }
B:A{ .m1 -> this; .m2 -> this.m1 }
"""));}
@Test void dispatchWhenMultipleCandidatesDisagree(){fail("""
002| B:A{ .m1 -> this; .m2 -> this.m1 }
   |      -------^^^^^

While inspecting parameter "this" > ".m1" line 2
The body of method ".m1" of type declaration "B" is an expression returning "mut B".
Parameter "this" has type "mut B" instead of a subtype of "A".

See inferred typing context below for how type "A" was introduced: (compression indicated by `-`)
B:A{.m1:A->this;mut .m1:A->this;.m2:A->this.m1}
""",List.of("""
A:{ imm .m1: A; mut .m1: A; .m2: A }
B:A{ .m1 -> this; .m2 -> this.m1 }
"""));}
@Test void dispatchWhenMultipleCandidatesAreCompatible(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; .m2: A }
B:A{ .m1 -> this; .m2 -> this.m1 }
"""));}
@Test void dispatchWithAnExplicitCapabilityOnTheOverride(){ok(List.of("""
A:{ imm .m1: A; mut .m1: A; .m2: A }
B:A{ imm .m1: A -> this; .m2: A -> this.m1 }
"""));}
@Test void callingMultiSig(){ok(List.of("""
A:{ read .m1: read B -> {}; mut .m1: mut A -> this }
B:{}
Test:{
  read .aRead(a: read A): read B -> a.m1;
  mut .aMut(a: mut A): mut A -> a.m1;
  }
"""));}
@Test void callingMultiSigWrongExpectedType(){fail("""
004|   read .aRead(a: read A): mut A -> a.m1;
   |   ---------------------------------^^^^^

While inspecting method call ".m1" > ".aRead(_)" line 4
The body of method ".aRead(_)" of type declaration "Test" is an expression returning "read B".
Method call "read A.m1" has type "read B" instead of a subtype of "mut A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
Test:{read .aRead(a:read A):mut A->a.m1[read];mut .aMut(a:mut A):mut A->a.m1[mut]}
""",List.of("""
A:{ read .m1: read B -> {}; mut .m1: mut A -> this }
B:{}
Test:{
  read .aRead(a: read A): mut A -> a.m1;
  mut .aMut(a: mut A): mut A -> a.m1;
  }
"""));}
@Test void callingMultiSigAmbiguousSameRet(){ok(List.of("""
A:{ read .m1: mut A -> {}; mut .m1: mut A -> this }
Test:{ read .aRead(a: mut A): mut A -> a.m1 }
"""));}
@Test void callingMultiSigImmPromotion(){ok(List.of("""
A:{ read .m1: mut A -> {}; mut .m1: mut A -> this }
Test:{ read .aRead(a: A): imm A -> a.m1 }
"""));}
@Test void callingMultiSigImmDispatch(){ok(List.of("""
A:{ read .m1: mut A -> {}; imm .m1: A -> this; mut .m1: mut A -> this }
Test:{ read .aRead(a: A): imm A -> a.m1 }
"""));}
@Test void oneMutHReceiverPromotesToMut(){ok(List.of("""
A:{ mut .m1: mut A -> this; .call(a: mutH A): mutH A -> a.m1 }
"""));}
@Test void oneMutHReceiverCannotProduceMut(){fail("""
001| A:{ mut .m1: mut A -> this; .call(a: mutH A): mut A -> a.m1 }
   |                             ---------------------------^^^^

While inspecting method call ".m1" > ".call(_)" line 1
The body of method ".call(_)" of type declaration "A" is an expression returning "mutH A".
Method call "mut A.m1" has type "mutH A" instead of a subtype of "mut A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{mut .m1:mut A->this;.call(a:mutH A):mut A->a.m1[mut]}
""",List.of("""
A:{ mut .m1: mut A -> this; .call(a: mutH A): mut A -> a.m1 }
"""));}
@Test void oneMutHArgumentPromotesInThirdPosition(){ok(List.of("""
A:{
  .m1(a1: imm A, a2: iso A, a3: mut A, a4: mut A): mut A -> a3;
  .call(a: mutH A): mutH A -> this.m1(imm A, iso A, a, iso A);
  }
"""));}
@Test void oneMutHArgumentPromotesInFourthPosition(){ok(List.of("""
A:{
  .m1(a1: imm A, a2: iso A, a3: mut A, a4: mut A): mut A -> a3;
  .call(a: mutH A): mutH A -> this.m1(imm A, iso A, iso A, a);
  }
"""));}
@Test void onlyOneMutHArgumentCanBePromoted(){fail("""
003|   .call(a: mutH A): mutH A -> this.m1(imm A, iso A, a, a);
   |   ----------------------------~~~~^^^^~~~~~~~~~~~~~~~~~~~

While inspecting ".call(_)" line 3
This call to method ".m1(_,_,_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "iso A" and is compatible with: Allow mutH argument 3, Allow mutH argument 4, Allow readH arguments, Allow mutH receiver, Allow mutH argument 1, Allow mutH argument 2, As declared, Strengthen result, Strengthen hygienic result.
- Argument 2 has type "iso A" and is compatible with: Allow mutH argument 3, Allow mutH argument 4, Allow readH arguments, Allow mutH receiver, Allow mutH argument 1, Allow mutH argument 2, As declared, Strengthen result, Strengthen hygienic result.
- Argument 3 has type "mutH A" and is compatible with: Allow mutH argument 3.
- Argument 4 has type "mutH A" and is compatible with: Allow mutH argument 4.

Promotion failures:
- Argument 3 fails:    As declared
  Parameter "a" has type "mutH A" instead of a subtype of "mut A".
- Argument 3 fails:    Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver, Allow mutH argument 1, Allow mutH argument 2, Allow mutH argument 4
  Parameter "a" has type "mutH A" instead of a subtype of "iso A".
- Argument 4 fails:    Allow mutH argument 3
  Parameter "a" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.m1(A,iso A,a,a)
""",List.of("""
A:{
  .m1(a1: imm A, a2: iso A, a3: mut A, a4: mut A): mut A -> a3;
  .call(a: mutH A): mutH A -> this.m1(imm A, iso A, a, a);
  }
"""));}
@Test void mutHReceiverAndMutHArgumentCannotBothBePromoted(){fail("""
003|   .call(a: mutH A): mutH A -> a.m1(imm A, iso A, a, iso A);
   |   ----------------------------~^^^^~~~~~~~~~~~~~~~~~~~~~~~

While inspecting ".call(_)" line 3
This call to method "mut A.m1(_,_,_,_)" cannot typecheck.
Argument 3 has type "mutH A".
Parameter "a" has type "mutH A" instead of a subtype of "iso A".

Type required by each promotion:
- "iso A"  (Allow mutH receiver)

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
A:{mut .m1(a1:A,a2:iso A,a3:mut A,a4:mut A):mut A->this;.call(a:mutH A):mutH A->a.m1[mut](A,iso A,a,iso A)}
""",List.of("""
A:{
  mut .m1(a1: imm A, a2: iso A, a3: mut A, a4: mut A): mut A -> this;
  .call(a: mutH A): mutH A -> a.m1(imm A, iso A, a, iso A);
  }
"""));}
@Test void noPromotionNeededWithFreshArguments(){ok(List.of("""
A:{
  .m1(a1: imm A, a2: iso A, a3: mut A, a4: mut A): mut A -> a3;
  .call(a: mutH A): mut A -> this.m1(imm A, iso A, mut A, mut A);
  }
"""));}
@Test void boxOfEverything(){ok(List.of(box));}
@Test void captureAsImmThroughMutGet(){ok(List.of("""
A:{ #(b: imm B): imm B -> Box#b.get }
B:{}
""",box));}
@Test void captureAsImmThroughReadImmGet(){ok(List.of("""
A:{ #(b: imm B): imm B -> Box#b.riget }
B:{}
""",box));}
@Test void captureAsImmThroughMutGetWithMethodGeneric(){ok(List.of("""
A:{ #[B:*](b: imm B): imm B -> Box#b.get }
""",box));}
@Test void immFromReadBox(){ok(List.of("""
A:{ #(b: read Box[imm B]): imm B -> b.riget }
B:{}
""",box));}
@Test void immFromReadBoxWithClassGeneric(){ok(List.of("""
A[B:*]:{ #(b: read Box[imm B]): imm B -> b.riget }
""",box));}
@Test void readImmOfAMutBoundedTypeVariable(){ok(List.of("""
A[X:mut]:{ #(x: X): read/imm X -> x }
"""));}
@Test void readImmOfAFullyBoundedTypeVariable(){fail("""
001| A[X:**]:{ #(x: X): read/imm X -> x }
   |           -----------------------^

While inspecting parameter "x" > "#(_)" line 1
The body of method "#(_)" of type declaration "A[_]" is an expression returning "X".
Parameter "x" has type "X" instead of a subtype of "read/imm X".

See inferred typing context below for how type "read/imm X" was introduced: (compression indicated by `-`)
A[X:**]:{#(x:X):read/imm X->x}
""",List.of("""
A[X:**]:{ #(x: X): read/imm X -> x }
"""));}
@Test void readParameterAcceptsAnyNonHygienicArgument(){ok(List.of("""
A:{ .m[X:*](x: read X): read X -> x }
B:{ .m[Y:*](y: Y): read Y -> A.m[Y](y) }
C:{ .m[Y:*](y: read Y): read Y -> A.m[Y](y) }
"""));}
@Test void readCannotBeLaunderedIntoImm(){fail("""
003| C:{ .m[Y:*](y: read Y): read/imm Y -> A.m[Y](y) }
   |     ----------------------------------~^^^~~~~~

While inspecting ".m(_)" line 3
This call to method "A.m(_)" cannot typecheck.
Argument 1 has type "read Y".
That is not a subtype of any of "read/imm Y" or "imm imm Y".
Parameter "y" has type "read Y" instead of a subtype of "read/imm Y".

Type required by each promotion:
- "read/imm Y"  (As declared)
- "imm imm Y"  (Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver, Allow mutH argument 1)

See inferred typing context below for how type "read/imm Y" was introduced: (compression indicated by `-`)
C:{.m[Y:*](y:read Y):read/imm Y->A.m[imm,Y](y)}
""",List.of("""
Foo:{}
A:{ .m[X:*](x: read/imm X): read/imm X -> x }
C:{ .m[Y:*](y: read Y): read/imm Y -> A.m[Y](y) }
D:{ .m(foo: read Foo): imm Foo -> C.m[imm Foo](foo) }
"""));}
@Test void readImmInheritance(){ok(List.of("""
B[Y:read,imm]:{ .m: read/imm Y }
A1[X:imm]:B[X]{}
A2[X:imm]:B[X]{ .m: read/imm X }
"""));}
@Test void passReadImmAround(){ok(List.of("""
B[X:*]:{
  .m1(a: read/imm X): read/imm X -> this.m1(a);
  .m2(a: read/imm X): read/imm X -> a;
  }
"""));}
@Test void passReadImmAroundWithMethodGeneric(){ok(List.of("""
B[X:*]:{
  .m1(a: read/imm X): read/imm X -> this.m1(a);
  .m2[Y:*](a: read/imm Y): read/imm Y -> a;
  }
"""));}
}
