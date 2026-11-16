package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public final class CapabilityTypingTest extends testUtils.FearlessTestBase{
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
Capability "iso" is not allowed on method declarations.
Allowed capabilities: "read", "mut", "imm".
""", List.of("""
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

While inspecting method call ".b" > method ".doThing" (line 1)
The body of method ".doThing" of type declaration "A" is an expression returning "mutH B".
Method call "read A.b" has type "mutH B" instead of a subtype of "mut B".

Relevant code with inferred types:
A:{read .b:mutH B->mut B;read .doThing:mut B->this.b[read]}
""", List.of("""
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
@Test void mutHResultIsLiteralWithMethods(){ok(List.of("""
A:{ .b(a: mut A): mutH B -> { .get -> a } }
B:{ mut .get: mut A }
"""));}
@Test void readHResultIsLiteralWithMethods(){ok(List.of("""
A:{ .b(a: read A): readH B -> { .get -> a } }
B:{ read .get: read A }
"""));}
@Test void mutHResultLiteralReadMethodCannotReturnMutCapture(){fail("""
002| ContainerF:{ #(a: mut A): mutH Container -> { .a1 -> a; .a2 -> a } }
   |              ---------------------------------~~~~~~~^------------

While inspecting parameter "a" > method ".a1" (line 2) > method "#(_)" (line 2)
Method ".a1" inside the object literal instance of "mut Container" (line 2) is implemented with an expression returning "read A".
Parameter "a" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capturing changes the type of parameter "a":
- "mut A" becomes "read A" inside the "read" method ".a1" (line 2).

Relevant code with inferred types:
ContainerF:{#(a:mut A):mutH Container->mut Container{read .a1:mut A->a;mut .a2:mut A->a}}
""", List.of("""
A:{}
ContainerF:{ #(a: mut A): mutH Container -> { .a1 -> a; .a2 -> a } }
Container:{ read .a1: mut A; mut .a2: mut A }
"""));}
@Test void thisOfAReadMethodIsReadWithNoDeclaredNote(){fail("""
001| A:{ read .me: mut A -> this }
   |     -------------------^^^^

While inspecting parameter "this" > method ".me" (line 1)
The body of method ".me" of type declaration "A" is an expression returning "read A".
Parameter "this" has type "read A" instead of a subtype of "mut A".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".me" (line 1).

Relevant code with inferred types:
A:{read .me:mut A->this}
""", List.of("""
A:{ read .me: mut A -> this }
"""));}
@Test void thisCapturedInALiteralOfAReadMethodIsRead(){fail("""
002| A:{ read .me: mut F -> mut F{ .get -> this } }
   |     --------------------------~~~~~~~~^^^^--

While inspecting parameter "this" > method ".get" (line 2) > method ".me" (line 2)
Method ".get" inside the object literal instance of "mut F" (line 2) is implemented with an expression returning "read A".
Parameter "this" has type "read A" instead of a subtype of "mut A".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".me" (line 2).

Relevant code with inferred types:
A:{read .me:mut F->mut F{mut .get:mut A->this}}
""", List.of("""
F:{ mut .get: mut A }
A:{ read .me: mut F -> mut F{ .get -> this } }
"""));}
@Test void thisCapturedInAReadMethodOfALiteralInAMutMethodHasNoDeclaredNote(){fail("""
002| A:{ mut .me: mut F -> mut F{ read .get -> this } }
   |     -------------------------~~~~~~~~~~~~~^^^^--

While inspecting parameter "this" > method ".get" (line 2) > method ".me" (line 2)
Method ".get" inside the object literal instance of "mut F" (line 2) is implemented with an expression returning "read A".
Parameter "this" has type "read A" instead of a subtype of "mut A".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".get" (line 2).

Relevant code with inferred types:
A:{mut .me:mut F->mut F{read .get:mut A->this}}
""", List.of("""
F:{ read .get: mut A }
A:{ mut .me: mut F -> mut F{ read .get -> this } }
"""));}
@Test void isoReceiverCapturedInALiteralIsImm(){fail("""
003| A:{ .m(b: iso B): F -> { b.x } }
   |     ---------------------^~~--

While inspecting method "#" (line 3) > method ".m(_)" (line 3)
This call to method "mut B.x" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".
Capturing changes the type of parameter "b":
- "iso B" becomes "imm B" inside the "mut" method "#" (line 3).

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
b.x[mut]
""", List.of("""
B:{ mut .x: B }
F:{ mut #: B }
A:{ .m(b: iso B): F -> { b.x } }
"""));}
@Test void thisReceiverOfAReadMethodIsRead(){fail("""
001| A:{ read .m: A -> this.mm; mut .mm: A -> A }
   |     --------------^^^^~~~

While inspecting method ".m" (line 1)
This call to method "mut A.mm" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".m" (line 1).

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.mm[mut]
""", List.of("""
A:{ read .m: A -> this.mm; mut .mm: A -> A }
"""));}
@Test void mutTypeVariableCaptureInReadMethodShowsDeclaredNote(){fail("""
002| A:{ .m[X:*](x: mut X): mut Get[mut X] -> mut Get[mut X]{ read .get: mut X -> x } }
   |     -----------------------------------------------------~~~~~~~~~~~~~~~~~~~~^--

While inspecting parameter "x" > method ".get" (line 2) > method ".m(_)" (line 2)
Method ".get" inside the object literal instance of "mut Get[mut X]" (line 2) is implemented with an expression returning "read X".
Parameter "x" has type "read X" instead of a subtype of "mut X".
Note: the declared type "mut X" would instead be a valid subtype.
Capturing changes the type of parameter "x":
- "mut X" becomes "read X" inside the "read" method ".get" (line 2).

Relevant code with inferred types:
A:{.m[X:*](x:mut X):mut Get[mut X]->mut Get[mut X]{read .get:mut X->x}}
""", List.of("""
Get[Y:*]:{ read .get: Y }
A:{ .m[X:*](x: mut X): mut Get[mut X] -> mut Get[mut X]{ read .get: mut X -> x } }
"""));}
@Test void noCallMutFromImm(){fail("""
002| A:{ .b: imm B -> {}; .doThing: Void -> this.b.foo.ret }
   |                      ------------------^^^^^^~~~~----

While inspecting method ".doThing" (line 2)
This call to method "mut B.foo" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.b.foo[mut]
""", List.of("""
Void:{}
A:{ .b: imm B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void noCallMutFromReadH(){fail("""
002| A:{ .b: readH B -> {}; .doThing: Void -> this.b.foo.ret }
   |                        ------------------^^^^^^~~~~----

While inspecting method ".doThing" (line 2)
This call to method "mut B.foo" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.b.foo[mut]
""", List.of("""
Void:{}
A:{ .b: readH B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void noCallMutFromRead(){fail("""
002| A:{ .b: read B -> {}; .doThing: Void -> this.b.foo.ret }
   |                       ------------------^^^^^^~~~~----

While inspecting method ".doThing" (line 2)
This call to method "mut B.foo" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.b.foo[mut]
""", List.of("""
Void:{}
A:{ .b: read B -> {}; .doThing: Void -> this.b.foo.ret }
B:{ mut .foo: mut B -> this; mut .ret: Void -> {} }
"""));}
@Test void readThisIsReadH(){ok(List.of("""
A:{ read .self: readH A -> this }
"""));}
@Test void noCaptureOfReadHInMutLiteral(){fail("""
002| B:{ .break(prisoner: readH B): mut A[readH B] -> {prisoner} }
   |     ----------------------------------------------^^^^^^^^-

While inspecting parameter "prisoner" > method ".prison" (line 2) > method ".break(_)" (line 2)
Parameter "prisoner" has type "readH B".
The type of parameter "prisoner" is hygienic ("readH" or "mutH") and thus parameter "prisoner" cannot be captured in the object literal instance of "mut A[readH B]" (line 2).
""", List.of("""
A[X:imm,mut,read,readH]:{ mut .prison: X }
B:{ .break(prisoner: readH B): mut A[readH B] -> {prisoner} }
"""));}
@Test void noCaptureOfHygienicTypeVariableInMutLiteral(){fail("""
002| B[X:mut,imm,read,mutH,readH]:{ .break(x: X): mut A[X] -> { x } }
   |                                ----------------------------^--

While inspecting parameter "x" > method ".prison" (line 2) > method ".break(_)" (line 2)
Parameter "x" has type "X".
The type of parameter "x" can be instantiated with a hygienic capability ("readH" or "mutH") and thus parameter "x" cannot be captured in the object literal instance of "mut A[X]" (line 2).
""", List.of("""
A[X:mut,imm,read,mutH,readH]:{ mut .prison: X }
B[X:mut,imm,read,mutH,readH]:{ .break(x: X): mut A[X] -> { x } }
"""));}
@Test void nominalPatternNextToHygienicParameter(){ok(List.of("""
P:{ read .a: P; read .b: P }
User:{ .m(bar: readH P, {.a, .b}: P): P -> bar.a }
"""));}
@Test void nominalPatternOf32NamesOnReadHParameter(){ok(List.of("""
P:{ read .a1: P; read .a2: P; read .a3: P; read .a4: P; read .a5: P; read .a6: P; read .a7: P; read .a8: P; read .a9: P; read .a10: P; read .a11: P; read .a12: P; read .a13: P; read .a14: P; read .a15: P; read .a16: P; read .a17: P; read .a18: P; read .a19: P; read .a20: P; read .a21: P; read .a22: P; read .a23: P; read .a24: P; read .a25: P; read .a26: P; read .a27: P; read .a28: P; read .a29: P; read .a30: P; read .a31: P; read .a32: P; }
User:{ .m({.a1, .a2, .a3, .a4, .a5, .a6, .a7, .a8, .a9, .a10, .a11, .a12, .a13, .a14, .a15, .a16, .a17, .a18, .a19, .a20, .a21, .a22, .a23, .a24, .a25, .a26, .a27, .a28, .a29, .a30, .a31, .a32}: readH P): P -> a32 }
"""));}
@Test void nominalPatternsOf32NamesInTotalOnReadHParameters(){ok(List.of("""
P:{ read .a1: P; read .a2: P; read .a3: P; read .a4: P; read .a5: P; read .a6: P; read .a7: P; read .a8: P; read .a9: P; read .a10: P; read .a11: P; read .a12: P; read .a13: P; read .a14: P; read .a15: P; read .a16: P; read .a17: P; read .a18: P; read .a19: P; read .a20: P; read .a21: P; read .a22: P; read .a23: P; read .a24: P; read .a25: P; read .a26: P; read .a27: P; read .a28: P; read .a29: P; read .a30: P; read .a31: P; read .a32: P; }
User:{ .m({.a1, .a2, .a3, .a4, .a5, .a6, .a7, .a8, .a9, .a10, .a11, .a12, .a13, .a14, .a15, .a16}: readH P, {.a17, .a18, .a19, .a20, .a21, .a22, .a23, .a24, .a25, .a26, .a27, .a28, .a29, .a30, .a31, .a32}: mutH P): P -> a17 }
"""));}
@Test void nominalPatternOfFiveNamesOnReadHParameter(){ok(List.of("""
P:{ read .a: P; read .b: P; read .c: P; read .d: P; read .e: P }
User:{ .m({.a, .b, .c, .d, .e}: readH P): P -> e }
"""));}
@Test void nominalPatternsOfFiveNamesWithMutHParameterLast(){ok(List.of("""
P:{ read .a: P; read .b: P; read .c: P; read .d: P; read .e: P }
User:{ .m({.d, .e}: P, {.a, .b, .c}: mutH P): P -> e }
"""));}
@Test void noReadImmEscapeFromIsoReceiver(){fail("""
004| C:{ #: mutH B -> A.m(B).absMeth }
   |     -------------^^^^^^^^^^^^^^

While inspecting method call ".absMeth" > method "#" (line 4)
The body of method "#" of type declaration "C" is an expression returning "B".
Method call "read L[_].absMeth" has type "B" instead of a subtype of "mutH B".

Relevant code with inferred types:
C:{#:mutH B->A.m[read](B).absMeth[read]}
""", List.of("""
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
   |     -----------------------------------------------------------------------------~~~~~~~~~~^^^-

While inspecting parameter "par" > method ".absMeth" (line 3) > method ".m(_)" (line 3)
Parameter "par" has type "T".
The type of parameter "par" can be instantiated with a hygienic capability ("readH" or "mutH") and thus parameter "par" cannot be captured in the object literal instance of "mut L[mutH T]" (line 3).
""", List.of("""
B:{}
L[X:mut,imm,read,readH,mutH]:{ mut .absMeth: imm X }
A:{ read .m[T:mut,imm,read,readH,mutH](par: T) : read L[mutH T] -> mut L[mutH T]{.absMeth->par} }
"""));}
@Test void noMutCaptureInIsoLiteral(){fail("""
003| A:{ read .m(par: mut B) : iso L -> iso L{.absMeth->par} }
   |     -------------------------------------~~~~~~~~~~^^^-

While inspecting parameter "par" > method ".absMeth" (line 3) > method ".m(_)" (line 3)
Parameter "par" has type "mut B".
Parameter "par" can observe mutation; thus it cannot be captured in the "iso" object literal instance of "L" (line 3).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
B:{}
L:{ mut .absMeth: mut B }
A:{ read .m(par: mut B) : iso L -> iso L{.absMeth->par} }
"""));}
@Test void noReadCaptureInImmLiteral(){fail("""
003| A:{ read .m(par: read B) : imm L -> imm L{.absMeth->par} }
   |     --------------------------------------~~~~~~~~~~^^^-

While inspecting parameter "par" > method ".absMeth" (line 3) > method ".m(_)" (line 3)
Parameter "par" has type "read B".
Parameter "par" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "L" (line 3).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
B:{}
L:{ imm .absMeth: read B }
A:{ read .m(par: read B) : imm L -> imm L{.absMeth->par} }
"""));}
@Test void isoLiteralCannotCaptureMut(){fail("""
002| Foos:{ #(a: mut A): iso Foo -> iso Foo{a} }
   |        --------------------------------^-

While inspecting parameter "a" > method "#" (line 2) > method "#(_)" (line 2)
Parameter "a" has type "mut A".
Parameter "a" can observe mutation; thus it cannot be captured in the "iso" object literal instance of "Foo" (line 2).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
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

While inspecting parameter "a" > method ".foo(_,_)" (line 2)
The body of method ".foo(_,_)" of type declaration "B" is an expression returning "mut A".
Parameter "a" has type "mut A" instead of a subtype of "iso A".

Relevant code with inferred types:
B:{.foo(a:mut A,aa:mutH A):iso A->a}
""", List.of("""
A:{ mut .a: iso A -> B.foo(this, this) }
B:{ .foo(a: mut A, aa: mutH A): iso A -> a }
"""));}
@Test void noIsoPromotionWithTwoMutArguments(){fail("""
002| B:{ .foo(a: mut A, aa: mut A): iso A -> a }
   |     ------------------------------------^

While inspecting parameter "a" > method ".foo(_,_)" (line 2)
The body of method ".foo(_,_)" of type declaration "B" is an expression returning "mut A".
Parameter "a" has type "mut A" instead of a subtype of "iso A".

Relevant code with inferred types:
B:{.foo(a:mut A,aa:mut A):iso A->a}
""", List.of("""
A:{ mut .a: iso A -> B.foo(this, this) }
B:{ .foo(a: mut A, aa: mut A): iso A -> a }
"""));}
@Test void noIsoPromotionWhenThisIsAlsoShared(){fail("""
002| B:{ .foo(a: mut A): iso A -> a }
   |     -------------------------^

While inspecting parameter "a" > method ".foo(_)" (line 2)
The body of method ".foo(_)" of type declaration "B" is an expression returning "mut A".
Parameter "a" has type "mut A" instead of a subtype of "iso A".

Relevant code with inferred types:
B:{.foo(a:mut A):iso A->a}
""", List.of("""
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

While inspecting method call ".name" > method ".mutate(_)" (line 3)
The body of method ".mutate(_)" of type declaration "Usage" is an expression returning "mutH Ref[Name]".
Method call "mut Person.name" has type "mutH Ref[Name]" instead of a subtype of "iso Ref[Name]".

Relevant code with inferred types:
Usage:{.mutate(p:mutH Person):iso Ref[Name]->p.name[mut]}
""", List.of("""
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
   |     -------------------------------------------------------^^~~~~-

While inspecting method ".break(_,_)" (line 2)
Iso parameter "x1" violates the single-use rule in method "A.break(_,_)" (line 2).
It is used directly 2 times.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.

Relevant code with inferred types:
this.break(x1,x1)
""", List.of("""
Caps:{} Void:{}
A:{ .break(x1: iso Caps, x2: iso Caps): Void -> this.break(x1, x1) }
"""));}
@Test void isoUsedDirectlyAndCaptured(){fail("""
003|   .break(x1: iso Caps, x2: iso Caps): Void -> this.breakTwo(x1, B{ x1 });
   |   ----------------------------------------------------------^^~~~~~~~---

While inspecting method ".break(_,_)" (line 3)
Iso parameter "x1" violates the single-use rule in method "A.break(_,_)" (line 3).
It is used directly and also captured into object literals.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.

Relevant code with inferred types:
this.breakTwo(x1,B{.x:Caps->x1})
""", List.of("""
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
@Test void immBoundedTypeVariableCapturedByALiteralInferredFromTheResult(){ok(List.of("""
A:{ #[X:imm](a: X): B[X] -> Block#(B[X]{a}, {a}) }
B[X:imm]:{ #: X }
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

While inspecting method call ".get" > method "#(_)" (line 3)
The body of method "#(_)" of type declaration "Test" is an expression returning "readH Foo".
Method call "read Box[_].get" has type "readH Foo" instead of a subtype of "Foo".

Relevant code with inferred types:
Test:{#(r:readH Box[Foo]):Foo->r.get[read]}
""", List.of("""
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
   |      -------^^^^

While inspecting parameter "this" > method ".m1" (line 2)
The body of method ".m1" of type declaration "B" is an expression returning "mut B".
Parameter "this" has type "mut B" instead of a subtype of "A".

Relevant code with inferred types:
B:A{.m1:A->this;mut .m1:A->this;.m2:A->this.m1}
""", List.of("""
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
   |   ---------------------------------^^^^

While inspecting method call ".m1" > method ".aRead(_)" (line 4)
The body of method ".aRead(_)" of type declaration "Test" is an expression returning "read B".
Method call "read A.m1" has type "read B" instead of a subtype of "mut A".

Relevant code with inferred types:
Test:{read .aRead(a:read A):mut A->a.m1[read];mut .aMut(a:mut A):mut A->a.m1[mut]}
""", List.of("""
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

While inspecting method call ".m1" > method ".call(_)" (line 1)
The body of method ".call(_)" of type declaration "A" is an expression returning "mutH A".
Method call "mut A.m1" has type "mutH A" instead of a subtype of "mut A".

Relevant code with inferred types:
A:{mut .m1:mut A->this;.call(a:mutH A):mut A->a.m1[mut]}
""", List.of("""
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
   |   ----------------------------~~~~^^^~~~~~~~~~~~~~~~~~~~~

While inspecting method ".call(_)" (line 3)
This call to method "A.m1(_,_,_,_)" cannot typecheck.
Arguments 3 and 4 need different promotions, but a call uses one promotion for all its arguments.
- Argument 3 has type "mutH A" and is compatible with: Allow mutH argument 3.
  Argument 3 fails with: Allow mutH argument 4.
  Parameter "a" has type "mutH A" instead of a subtype of "iso A".
- Argument 4 has type "mutH A" and is compatible with: Allow mutH argument 4.
  Argument 4 fails with: Allow mutH argument 3.
  Parameter "a" has type "mutH A" instead of a subtype of "iso A".

Relevant code with inferred types:
this.m1(A,iso A,a,a)
""", List.of("""
A:{
  .m1(a1: imm A, a2: iso A, a3: mut A, a4: mut A): mut A -> a3;
  .call(a: mutH A): mutH A -> this.m1(imm A, iso A, a, a);
  }
"""));}
@Test void mutHReceiverAndMutHArgumentCannotBothBePromoted(){fail("""
003|   .call(a: mutH A): mutH A -> a.m1(imm A, iso A, a, iso A);
   |   ----------------------------~~~~~~~~~~~~~~~~~~~^~~~~~~~~

While inspecting method ".call(_)" (line 3)
This call to method "mut A.m1(_,_,_,_)" cannot typecheck.
Argument 3 has type "mutH A".
Parameter "a" has type "mutH A" instead of a subtype of "iso A".

Type required by each promotion:
- "iso A" (Allow mutH receiver)

Relevant code with inferred types:
A:{mut .m1(a1:A,a2:iso A,a3:mut A,a4:mut A):mut A->this;.call(a:mutH A):mutH A->a.m1[mut](A,iso A,a,iso A)}
""", List.of("""
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
""", box));}
@Test void captureAsImmThroughReadImmGet(){ok(List.of("""
A:{ #(b: imm B): imm B -> Box#b.riget }
B:{}
""", box));}
@Test void captureAsImmThroughMutGetWithMethodGeneric(){ok(List.of("""
A:{ #[B:*](b: imm B): imm B -> Box#b.get }
""", box));}
@Test void immFromReadBox(){ok(List.of("""
A:{ #(b: read Box[imm B]): imm B -> b.riget }
B:{}
""", box));}
@Test void immFromReadBoxWithClassGeneric(){ok(List.of("""
A[B:*]:{ #(b: read Box[imm B]): imm B -> b.riget }
""", box));}
@Test void readImmOfAMutBoundedTypeVariable(){ok(List.of("""
A[X:mut]:{ #(x: X): read/imm X -> x }
"""));}
@Test void readImmOfAFullyBoundedTypeVariable(){fail("""
001| A[X:**]:{ #(x: X): read/imm X -> x }
   |           -----------------------^

While inspecting parameter "x" > method "#(_)" (line 1)
The body of method "#(_)" of type declaration "A[_]" is an expression returning "X".
Parameter "x" has type "X" instead of a subtype of "read/imm X".

Relevant code with inferred types:
A[X:**]:{#(x:X):read/imm X->x}
""", List.of("""
A[X:**]:{ #(x: X): read/imm X -> x }
"""));}
@Test void readParameterAcceptsAnyNonHygienicArgument(){ok(List.of("""
A:{ .m[X:*](x: read X): read X -> x }
B:{ .m[Y:*](y: Y): read Y -> A.m[Y](y) }
C:{ .m[Y:*](y: read Y): read Y -> A.m[Y](y) }
"""));}
@Test void readCannotBeLaunderedIntoImm(){fail("""
003| C:{ .m[Y:*](y: read Y): read/imm Y -> A.m[Y](y) }
   |     ----------------------------------~~~~~~~^~

While inspecting method ".m(_)" (line 3)
This call to method "A.m(_)" cannot typecheck.
Argument 1 has type "read Y".
Parameter "y" has type "read Y" instead of a subtype of "read/imm Y".

Type required by each promotion:
- "read/imm Y" (As declared)
- "imm Y" (Strengthen result)

Relevant code with inferred types:
C:{.m[Y:*](y:read Y):read/imm Y->A.m[imm,Y](y)}
""", List.of("""
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
@Test void genericReadHBoxReadImmGetIsNotRead(){fail("""
[###]Method call "read Box[_].get" has type "readH Y" instead of a subtype of "read Y".
[###]
""", List.of("""
Box[X:*]:{ mut .get: X; read .get: read/imm X }
Test:{ #[Y:mut](r: readH Box[Y]): read Y -> r.get }
"""));}
@Test void genericReadHBoxReadImmGetOfReadHIsNotRead(){fail("""
[###]Method call "read Box[_].get" has type "readH Y" instead of a subtype of "read Y".
[###]
""", List.of("""
Box[X:**]:{ mut .get: X; read .get: read/imm X }
Test:{ #[Y:readH](r: readH Box[Y]): read Y -> r.get }
"""));}
@Test void genericReadHSinkAcceptsReadHReadImmArgument(){ok(List.of("""
Void:{}
Sink[X:*]:{ read .put(x: read/imm X): Void }
Test:{ #[Y:mut](s: readH Sink[Y], y: readH Y): Void -> s.put(y) }
"""));}
@Test void readImmResultOfIsoImmBoundRequiredAsImm(){ok(List.of("""
Box[X:iso,imm]:{ .get: read/imm X }
User:{ .use[Y:iso,imm](b: Box[Y]): imm Y -> b.get }
"""));}
@Test void readImmResultOfIsoImmBoundRequiredAsReadImm(){ok(List.of("""
Box[X:iso,imm]:{ .get: read/imm X }
User:{ .use[Y:iso,imm](b: Box[Y]): read/imm Y -> b.get }
"""));}
@Test void readImmResultOfIsoImmBoundRequiredAsIso(){fail("""
002| User:{ .use[Y:iso,imm](b: Box[Y]): iso Y -> b.get }
   |        -------------------------------------^^^^^

While inspecting method call ".get" > method ".use(_)" (line 2)
The body of method ".use(_)" of type declaration "User" is an expression returning "read/imm Y".
Method call "Box[_].get" has type "read/imm Y" instead of a subtype of "iso Y".

Relevant code with inferred types:
User:{.use[Y:imm,iso](b:Box[Y]):iso Y->b.get}
""", List.of("""
Box[X:iso,imm]:{ .get: read/imm X }
User:{ .use[Y:iso,imm](b: Box[Y]): iso Y -> b.get }
"""));}
@Test void readImmResultOfIsoImmBoundAsReceiver(){fail("""
002| User:{ .use[Y:iso,imm](b: Box[Y]): Box[Y] -> b.get.foo }
   |        --------------------------------------^^^^^~~~~

While inspecting method ".use(_)" (line 2)
This call to method ".foo" cannot typecheck.
The receiver has type "read/imm Y", where "Y" is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

Relevant code with inferred types:
User:{.use[Y:imm,iso](b:Box[Y]):Box[Y]->b.get.foo}
""", List.of("""
Box[X:iso,imm]:{ .get: read/imm X }
User:{ .use[Y:iso,imm](b: Box[Y]): Box[Y] -> b.get.foo }
"""));}
@Test void readHEmptyLiteralLeavesMutAbstract(){ok(List.of("""
B:{ mut .m: B }
A:{ .b: readH B -> {} }
"""));}
@Test void readHEmptyLiteralArgumentLeavesMutAbstract(){ok(List.of("""
B:{ mut .m: B }
A:{ .f(b: readH B): A -> this; .g: A -> this.f({}) }
"""));}
@Test void readHLiteralWithBodyLeavesMutAbstract(){ok(List.of("""
C:{}
B:{ mut .m: B; .k: C }
A:{ .b: readH B -> { .k -> {} } }
"""));}
@Test void readHLambdaArgumentLeavesMutOverloadAbstract(){ok(List.of("""
A:{}
Box:{ mut .get: A; read .get: A; }
Need:{ #(b: readH Box): A -> A }
User:{
  read .a: A -> A;
  read .f: A -> Need#{ .get -> this.a };
}
"""));}
@Test void readHLambdaResultLeavesMutOverloadAbstract(){ok(List.of("""
A:{}
Box:{ mut .get: A; read .get: A; }
User:{
  read .a: A -> A;
  read .f: readH Box -> { .get -> this.a };
}
"""));}
@Test void mutHLambdaArgumentImplementsBothOverloads(){ok(List.of("""
A:{}
Box:{ mut .get: A; read .get: A; }
Need:{ #(b: mutH Box): A -> A }
User:{
  read .a: A -> A;
  read .f: A -> Need#{ .get -> this.a };
}
"""));}
@Test void mutHEmptyLiteralMustImplementMut(){fail("""
002| A:{ .b: mutH B -> {} }
   |     --------------^^

While inspecting object literal instance of "mut B" > method ".b" (line 2)
This object literal is missing a required method.
Missing: "mut .m".
Required by: "B".
Add an implementation for ".m" inside the object literal.
""", List.of("""
B:{ mut .m: B }
A:{ .b: mutH B -> {} }
"""));}
@Test void mutArgumentPassedAsReadKeepsMutOverload(){ok(List.of("""
A:{ imm .a:A->A; read .a:A->A; mut .a:A->A; }
Use:{ #(a: read A): A -> A; }
Two:{ #(a1: A, a2: A): A -> a1; }
User:{ .m(x: mut A): A -> Two#(Use#(x), x.a); }
"""));}
@Test void mutArgumentPassedAsReadThenMutCall(){ok(List.of("""
B:{}
A:{ read .a:B->B; mut .a:mut B->mut B{}; }
Use:{ #(a: read A): B -> B; }
Two:{ #(a1: B, a2: mut B): B -> a1; }
User:{ .m(x: mut A): B -> Two#(Use#(x), x.a); }
"""));}
@Test void readArgumentPassedAsReadHKeepsReadOverload(){ok(List.of("""
A:{ imm .a:A->A; read .a:A->A; mut .a:A->A; }
Use:{ #(a: readH A): A -> A; }
Two:{ #(a1: A, a2: A): A -> a1; }
User:{ .m(x: read A): A -> Two#(Use#(x), x.a); }
"""));}
@Test void mutArgumentPassedAsMutHKeepsMutOverload(){ok(List.of("""
A:{ imm .a:A->A; read .a:A->A; mut .a:A->A; }
Use:{ #(a: mutH A): A -> A; }
Two:{ #(a1: A, a2: A): A -> a1; }
User:{ .m(x: mut A): A -> Two#(Use#(x), x.a); }
"""));}
@Test void mutCaptureReturnedAsReadKeepsMutOverload(){ok(List.of("""
A:{ imm .a:A->A; read .a:A->A; mut .a:A->A; }
F:{ mut #: read A; }
Two:{ #(f: mut F, a2: A): A -> a2; }
User:{ .m(x: mut A): A -> Two#(mut F{ # -> x }, x.a); }
"""));}
@Test void mutGenericArgumentPassedAsReadKeepsMutTypeArgument(){ok(List.of("""
B:{}
Id:{ #[Y:imm,mut,read](y: Y): Y -> y; }
User[X:mut]:{
  .use(a: read X): B -> B;
  .two(b: B, y: mut X): mut X -> y;
  .m(x: mut X): mut X -> this.two(this.use(x), Id#(x));
}
"""));}
@Test void mutArgumentToGenericWithReadResultInfersMut(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: Y): Y -> y }
A:{ .g(x: mut Foo): read Foo -> Util.m(x) }
"""));}
@Test void mutTypeVariableArgumentToGenericWithReadResultInfersMut(){ok(List.of("""
Util:{ .m[Y:*](y: Y): Y -> y }
A:{ .f[X:*](x: mut X): read X -> Util.m(x) }
"""));}
@Test void readImmResultInfersCapabilityWhenLambdaReturnsSubtype(){ok(List.of("""
Cat:{}
ToFl[E:*]:{ read .seq: mut Fl[read/imm E]; mut .seq: mut Fl[E]; }
Li[E:*]:ToFl[E]{}
Fl[E:*]:{
  mut .viaToFl[R:*](f: read base.F[E, read ToFl[R]]): mut Fl[read/imm R];
  mut .li: mut Li[E];
  }
Person:{ read .cats: Li[Cat] }
User:{ #(f: mut Fl[Person]): mut Li[Cat] -> f.viaToFl{::.cats}.li }
"""));}
@Test void readImmResultThenFoldInfersTheExactTypeArgument(){ok(List.of("""
Item:{}
ToFl[E:*]:{ read .seq: mut Fl[read/imm E]; mut .seq: mut Fl[E]; }
Li[E:*]:ToFl[E]{ mut +>(e: E): mut Li[E]; read +>(e: read E): read Li[E]; }
Fl[E:*]:{
  mut .viaToFl[R:*](f: read base.F[E, read ToFl[R]]): mut Fl[read/imm R];
  mut .fold[R:*](acc: iso base.MF[R], f: read base.F[R,E,R]): R;
  }
User:{ #(f: mut Fl[mut Li[Item]]): Li[Item] -> f.viaToFl{c -> c}.fold({base.Nope!}, {acc, i -> acc +> i}) }
"""));}
@Test void lambdaReturningSubtypeDeterminesTypeArgument(){ok(List.of("""
Item:{}
ToFl[E:*]:{ read .seq: mut Fl[read/imm E]; mut .seq: mut Fl[E]; }
Li[E:*]:ToFl[E]{}
Fl[E:*]:{ mut .viaToFl[R:*](f: read base.F[E, read ToFl[R]]): mut Fl[R]; }
User:{
  .any[X:**](x: X): Item -> Item;
  #(f: mut Fl[mut Li[Item]]): Item -> this.any(f.viaToFl{c -> c});
  }
"""));}
@Test void lambdaBodyReturningMutDoesNotRefineAnImmTypeArgument(){ok(List.of("""
Cat:{}
Li[E:*]:{}
Lis:{ #[E:*](e: E): mut Li[E] -> base.Nope! }
OM[E:*,R:**]:{ mut .empty: R; mut .some(x: E): R; }
Op[E:*]:{ imm .match[R:**](m: mut OM[imm E, R]): R; }
Take:{ #[R:*](xs: Li[R]): Li[R] -> xs }
User:{ #(o: Op[Cat]): Li[Cat] -> Take#(o.match{.empty -> {}; .some x -> Lis#x}) }
"""));}
@Test void lambdaBodyReturningMutWithExpectedTypeKnown(){ok(List.of("""
Cat:{}
Li[E:*]:{}
Lis:{ #[E:*](e: E): mut Li[E] -> base.Nope! }
OM[E:*,R:**]:{ mut .empty: R; mut .some(x: E): R; }
Op[E:*]:{ imm .match[R:**](m: mut OM[imm E, R]): R; }
Take:{ #[R:*](xs: Li[R]): Li[R] -> xs }
User:{ #(o: Op[Cat]): Li[Cat] -> o.match{.empty -> {}; .some x -> Lis#x} }
"""));}
@Test void lambdaBodyReturningMutWithWrittenOuterTypeArgument(){ok(List.of("""
Cat:{}
Li[E:*]:{}
Lis:{ #[E:*](e: E): mut Li[E] -> base.Nope! }
OM[E:*,R:**]:{ mut .empty: R; mut .some(x: E): R; }
Op[E:*]:{ imm .match[R:**](m: mut OM[imm E, R]): R; }
Take:{ #[R:*](xs: Li[R]): Li[R] -> xs }
User:{ #(o: Op[Cat]): Li[Cat] -> Take#[Cat](o.match{.empty -> {}; .some x -> Lis#x}) }
"""));}
@Test void lambdaArgumentThroughCapabilityOnTypeVariableLeavesItOpen(){ok(List.of("""
N:{}
By[T:*,K:*]:{ read #(t: read T): K }
M:{ .max[T:*,K:*](by: By[imm T,K], t0: T, t1: T): T -> t0 }
User:{ #(a: N, b: N): N -> M.max({t -> t}, a, b) }
"""));}
@Test void readImmResultInfersCapabilityWhenLambdaReturnsExactType(){ok(List.of("""
Cat:{}
ToFl[E:*]:{ read .seq: mut Fl[read/imm E]; mut .seq: mut Fl[E]; }
Li[E:*]:ToFl[E]{}
Fl[E:*]:{
  mut .viaLi[R:*](f: read base.F[E, read Li[R]]): mut Fl[read/imm R];
  mut .li: mut Li[E];
  }
Person:{ read .cats: Li[Cat] }
User:{ #(f: mut Fl[Person]): mut Li[Cat] -> f.viaLi{::.cats}.li }
"""));}
@Test void mutArgumentToReadImmParameterInfersMut(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: read/imm Y): Foo -> Foo }
A:{ .f(x: mut Foo): Foo -> Util.m(x) }
"""));}
@Test void mutTypeVariableArgumentToReadImmParameterInfersMut(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: read/imm Y): Foo -> Foo }
A:{ .f[X:*](x: mut X): Foo -> Util.m(x) }
"""));}
@Test void readMethodCaptureOfTypeParamInfersReadImmTypeArg(){ok(List.of("""
Nothing:{}
Ignore:{ #[T:*](t: T): Nothing -> Nothing }
Holder:{ read .n: Nothing }
User:{ .m[X:*](x: X): mut Holder -> mut Holder{ .n -> Ignore#x } }
"""));}
@Test void readMethodCaptureOfTypeParamExplicitTypeArgOk(){ok(List.of("""
Nothing:{}
Ignore:{ #[T:*](t: T): Nothing -> Nothing }
Holder:{ read .n: Nothing }
User:{ .m[X:*](x: X): mut Holder -> mut Holder{ .n -> Ignore#[read/imm X](x) } }
"""));}
@Test void mutMethodCaptureOfIsoImmTypeParamInfersImmTypeArg(){ok(List.of("""
Nothing:{}
Ignore:{ #[T:*](t: T): Nothing -> Nothing }
Holder:{ mut .n: Nothing }
User:{ .m[X:iso,imm](x: X): mut Holder -> mut Holder{ .n -> Ignore#x } }
"""));}
@Test void mutMethodCaptureOfIsoMutTypeParamInfersReadImmTypeArg(){ok(List.of("""
Nothing:{}
Ignore:{ #[T:*](t: T): Nothing -> Nothing }
Holder:{ mut .n: Nothing }
User:{ .m[X:iso,mut](x: X): mut Holder -> mut Holder{ .n -> Ignore#x } }
"""));}
@Test void mutMethodCaptureOfIsoMutTypeParamIsReadImm(){ok(List.of("""
Get[Y:*]:{ mut .get: Y }
A:{ .m[X:iso,mut](x: X): mut Get[read/imm X] -> mut Get[read/imm X]{ mut .get: read/imm X -> x } }
"""));}
@Test void mutMethodCaptureOfIsoReadTypeParamIsReadImm(){ok(List.of("""
Get[Y:*]:{ mut .get: Y }
A:{ .m[X:iso,read](x: X): mut Get[read/imm X] -> mut Get[read/imm X]{ mut .get: read/imm X -> x } }
"""));}
@Test void mutMethodCaptureOfIsoMutTypeParamIsNotX(){fail("""
002| A:{ .m[X:iso,mut](x: X): mut Get[X] -> mut Get[X]{ mut .get: X -> x } }
   |     -----------------------------------------------~~~~~~~~~~~~~~~^--

While inspecting parameter "x" > method ".get" (line 2) > method ".m(_)" (line 2)
Method ".get" inside the object literal instance of "mut Get[X]" (line 2) is implemented with an expression returning "read/imm X".
Parameter "x" has type "read/imm X" instead of a subtype of "X".
Note: the declared type "X" would instead be a valid subtype.
Capturing changes the type of parameter "x":
- "X" becomes "read/imm X" inside the "mut" method ".get" (line 2).

Relevant code with inferred types:
A:{.m[X:mut,iso](x:X):mut Get[X]->mut Get[X]{mut .get:X->x}}
""", List.of("""
Get[Y:**]:{ mut .get: Y }
A:{ .m[X:iso,mut](x: X): mut Get[X] -> mut Get[X]{ mut .get: X -> x } }
"""));}
@Test void readMethodCaptureOfIsoMutTypeParamInfersReadImmTypeArg(){ok(List.of("""
Nothing:{}
Id:{ #[T:*](t: T): T -> t }
Need[X:iso,mut]:{ #(y: read/imm X): Nothing -> Nothing }
Holder:{ read .n: Nothing }
User:{ .m[X:iso,mut](x: X): mut Holder -> mut Holder{ .n -> Need[X]#(Id#x) } }
"""));}
@Test void literalKeepsDecidedReadImmXAgainstImmXBody(){ok(List.of("""
Get[Y:*]:{ read .get: Y }
A:{ .m[X:imm,read](y: imm X): mut Get[read/imm X] -> { .get -> y } }
"""));}
@Test void writtenLiteralKeepsItsReadImmXTypeArgument(){ok(List.of("""
Get[Y:*]:{ read .get: Y }
A:{ .n[X:imm,read](y: imm X): mut Get[read/imm X] -> mut Get[read/imm X]{ read .get: read/imm X -> y } }
"""));}
@Test void readArgumentToReadTypeVariableParameterExplicitTypeArgumentOk(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: read Y): Foo -> Foo }
A:{ .f(x: read Foo): Foo -> Util.m[Foo](x) }
"""));}
@Test void readArgumentToReadTypeVariableParameterInfersItsTypeArgument(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: read Y): Foo -> Foo }
A:{ .f(x: read Foo): Foo -> Util.m(x) }
"""));}
@Test void immArgumentToImmTypeVariableParameterInfersItsTypeArgument(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: imm Y): Foo -> Foo }
A:{ .f(x: Foo): Foo -> Util.m(x) }
"""));}
@Test void readResultOfReadTypeVariableInfersItsTypeArgument(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*]: read Y -> this.m[Y] }
A:{ .f: read Foo -> Util.m }
"""));}
@Test void lambdaWithReadParameterInfersItsSupertypeTypeArgument(){ok(List.of("""
Foo:{}
Cons[Y:*]:{ #(y: read Y): Foo }
Need:{ #[Y:*](c: Cons[Y]): Foo -> Foo }
A:{ .f: Foo -> Need#{ #(y: read Foo): Foo -> Foo } }
"""));}
@Test void isoArgumentToTypeVariableWithoutIsoBoundInfersItsTypeArgument(){ok(List.of("""
Foo:{}
Util:{ .m[Y:*](y: Y): Foo -> Foo }
A:{ .f(x: iso Foo): Foo -> Util.m(x) }
"""));}
@Test void readArgumentToReadTypeVariableWithoutImmBoundInfersItsTypeArgument(){ok(List.of("""
Foo:{}
Util:{ .m[Y:mut,read](y: read Y): Foo -> Foo }
A:{ .f(x: read Foo): Foo -> Util.m(x) }
"""));}
@Test void lambdaWithReadParameterWithoutImmBoundInfersItsSupertypeTypeArgument(){ok(List.of("""
Foo:{}
Cons[Y:mut,read]:{ #(y: read Y): Foo }
Need:{ #[Y:mut,read](c: Cons[Y]): Foo -> Foo }
A:{ .f: Foo -> Need#{ #(y: read Foo): Foo -> Foo } }
"""));}
}