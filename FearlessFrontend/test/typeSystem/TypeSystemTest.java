package typeSystem;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Test;

import core.LiteralDeclarations;

public final class TypeSystemTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failExt(String expected, List<String> input){ typeFailRaw(expected, input); }
  static void failWf(String expected, List<String> input){ typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input); }

@Test void tsMiniOk(){ok(List.of("""
A:{.foo123:A->this.foo123}
"""));}
@Test void anonLiteralInDuplicatedBody(){ok(List.of("""
A:{ .k: A -> this }
T0:{ .m: A; }
T1:T0{ read .m: A -> A }
U:{ .u: T1 -> T1{ .m: A -> A{ .k: A -> A } } }
"""));}
@Test void manyConsecutiveLetsInOneMethod(){
  var lets= IntStream.rangeClosed(1, 150).mapToObj(i -> ".let x"+i+"= {5} ").collect(Collectors.joining());
  ok(List.of("use base.Nat as Nat; User:{ .u: Nat -> base.Block#"+lets+".return {x150} }"));}
@Test void manyNestedLiterals(){
  var open= IntStream.range(0, 300).mapToObj(_ -> "A{ .a -> ").collect(Collectors.joining());
  ok(List.of("A:{ .a: A } User:{ .u: A -> "+open+"A{ .a -> this.u }"+" }".repeat(300)+" }"));}
@Test void expansiveSupertypeArgumentNotASubtype(){fail("""
002| T1:T0[T0[T1]]{ .m(a: T0[T1]): T1 -> this.m(this) }
   |                ---------------------~~~~~~~^^^^~

While inspecting method ".m(_)" (line 2)
This call to method "T1.m(_)" cannot typecheck.
Argument 1 has type "T1".
That is not a subtype of "T0[T1]" (the type required by the method signature).

Relevant code with inferred types:
this.m(this)
""", List.of("""
T0[X]:{ }
T1:T0[T0[T1]]{ .m(a: T0[T1]): T1 -> this.m(this) }
"""));}
@Test void stringLiteralsWithACommaOrACurlyBrace(){ok(List.of("B:{ .m(s: base.Str): B -> this } A:{ .m(b: B): B -> b.m(\"a, b\").m(\"{\").m(`c, d`) }"));}
@Test void expansiveSupertypeArgument(){ok(List.of("""
T0[X]:{ }
T1:T0[T0[T1]]{ .m(a: T0[T0[T1]]): T1 -> this.m(this) }
"""));}
@Test void expansiveSupertypeResultNotASubtype(){fail("""
002| T1:T0[T0[T1]]{ .m: T0[T1] -> this }
   |                --------------^^^^

While inspecting parameter "this" > method ".m" (line 2)
The body of method ".m" of type declaration "T1" is an expression returning "T1".
Parameter "this" has type "T1" instead of a subtype of "T0[T1]".

Relevant code with inferred types:
T1:T0[T0[T1]]{.m:T0[T1]->this}
""", List.of("""
T0[X]:{ }
T1:T0[T0[T1]]{ .m: T0[T1] -> this }
"""));}
@Test void expansiveGenericSupertypeArgumentNotASubtype(){fail("""
002| T1[X]:T0[T0[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
   |                      ---------------------------~~~~~~~^^^^~

While inspecting method ".m(_)" (line 2)
This call to method "T1[_].m(_)" cannot typecheck.
Argument 1 has type "T1[X]".
That is not a subtype of "T0[T1[X]]" (the type required by the method signature).

Relevant code with inferred types:
this.m(this)
""", List.of("""
T0[X]:{ }
T1[X]:T0[T0[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
"""));}
@Test void expansiveGenericSupertypeArgument(){ok(List.of("""
T0[X]:{ }
T1[X]:T0[T0[T1[X]]]{ .m(a: T0[T0[T1[X]]]): T1[X] -> this.m(this) }
"""));}
@Test void growingSupertypeArgumentNotASubtype(){fail("""
002| T1[X]:T0[T1[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
   |                      ---------------------------~~~~~~~^^^^~

While inspecting method ".m(_)" (line 2)
This call to method "T1[_].m(_)" cannot typecheck.
Argument 1 has type "T1[X]".
That is not a subtype of "T0[T1[X]]" (the type required by the method signature).

Relevant code with inferred types:
this.m(this)
""", List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
"""));}
@Test void growingSupertypeArgument(){ok(List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m(a: T0[T1[T1[X]]]): T1[X] -> this.m(this) }
"""));}
@Test void growingSupertypeResultNotASubtype(){fail("""
002| T1[X]:T0[T1[T1[X]]]{ .m: T0[T1[X]] -> this }
   |                      -----------------^^^^

While inspecting parameter "this" > method ".m" (line 2)
The body of method ".m" of type declaration "T1[_]" is an expression returning "T1[X]".
Parameter "this" has type "T1[X]" instead of a subtype of "T0[T1[X]]".

Relevant code with inferred types:
T1[X]:T0[T1[T1[X]]]{.m:T0[T1[X]]->this}
""", List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m: T0[T1[X]] -> this }
"""));}
@Test void growingSupertypeResult(){ok(List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m: T0[T1[T1[X]]] -> this }
"""));}
@Test void growingSupertypeInfersMethodTypeArgument(){ok(List.of("""
T0[X]:{ .get: X }
T1[X]:T0[T1[T1[X]]]{ .m[Y](a: T0[Y]): Y -> a.get; .k: T1[T1[X]] -> this.m(this) }
"""));}
@Test void growingSupertypeInfersMethodTypeArgumentNotASubtype(){fail("""
002| T1[X]:T0[T1[T1[X]]]{ .m[Y](a: T0[Y]): Y -> a.get; .k: T1[X] -> this.m(this) }
   |                                                   -------------^^^^^^^^^^^^

While inspecting method call ".m(_)" > method ".k" (line 2)
The body of method ".k" of type declaration "T1[_]" is an expression returning "T1[T1[X]]".
Method call "T1[_].m(_)" has type "T1[T1[X]]" instead of a subtype of "T1[X]".

Relevant code with inferred types:
T1[X]:T0[T1[T1[X]]]{.m[Y](a:T0[Y]):Y->a.get;.k:T1[X]->this.m[imm,T1[T1[X]]](this)}
""", List.of("""
T0[X]:{ .get: X }
T1[X]:T0[T1[T1[X]]]{ .m[Y](a: T0[Y]): Y -> a.get; .k: T1[X] -> this.m(this) }
"""));}
@Test void receiverLiteralWithUndeterminedTypeArguments(){failWf("""
001| T0[X0,X1]:{ .m2(x: X0): base.Void; .m0: T0[X0, base.Void] -> {}.m0 }
   |                                                              ^^

While inspecting object literal instance of "T0[_,_]"
Type inference concluded that this object literal implements "T0[?,?]",
but it could not infer generic type arguments 1 and 2 for generic type parameters "X0" and "X1" of "T0[_,_]".
Write the generic type arguments explicitly, as in "T0[Type1,Type2]{...}".
""", List.of("""
T0[X0,X1]:{ .m2(x: X0): base.Void; .m0: T0[X0, base.Void] -> {}.m0 }
"""));}
@Test void receiverLiteralCapturingThis(){failWf("""
001| T0[X]:{ .m: T0[base.Void] -> {this}.m }
   |                              ^^^^^^

While inspecting object literal instance of "T0[_]"
Type inference concluded that this object literal implements "T0[?]",
but it could not infer generic type argument 1 for generic type parameter "X" of "T0[_]".
Write the generic type argument explicitly, as in "T0[Type1]{...}".
""", List.of("""
T0[X]:{ .m: T0[base.Void] -> {this}.m }
"""));}
@Test void methodTypeParameterOnlyInLiteralResult(){fail("""
002| T1:{ .m[Y]: T1 -> { .k: Z[Y] -> this } }
   |      ---------------~~~~~~~~~~~~^^^^--

While inspecting parameter "this" > method ".k" (line 2) > method ".m" (line 2)
Method ".k" inside the object literal instance of "T1" (line 2)
is implemented with an expression returning "T1".
Parameter "this" has type "T1" instead of a subtype of "Z[Y]".

Relevant code with inferred types:
T1:{.m[Y]:T1->T1{.k:Z[Y]->this}}
""", List.of("""
Z[X]:{ }
T1:{ .m[Y]: T1 -> { .k: Z[Y] -> this } }
"""));}
@Test void freshMethodGenericMustNotCaptureInheritedSiblingGeneric(){ok(List.of("""
A:{ .foo[_AX,X](a:_AX,b:X):A; }
B[X]:A{ .foo(a,b)->this }
User:{ .m(b:B[User]):A -> b.foo[User,A](this,b) }
"""));}
@Test void freshMethodGenericMustKeepInheritedGenericsDistinct(){fail("""
002| B[X]:A{ .foo(a,b)->b }
   |         -----------^

While inspecting parameter "b" > method ".foo(_,_)" (line 2)
The body of method ".foo(_,_)" of type declaration "B[_]" is an expression returning "_BX".
Parameter "b" has type "_BX" instead of a subtype of "_AX".

Name "_BX" stands for generic type parameter "X" of an inherited method, renamed because "X" already names a type or another generic type parameter.

Relevant code with inferred types:
B[X]:A{.foo[_AX,_BX](a:_AX,b:_BX):_AX->b}
""", List.of("""
A:{ .foo[_AX,X](a:_AX,b:X):_AX; }
B[X]:A{ .foo(a,b)->b }
"""));}
@Test void keptInheritedMethodGenericMustNotBeCapturedByNestedLiteral(){ok(List.of("""
F[T]:{ .k[X](y:X):T; }
Sup:{ .m[X](x:X):F[X]; }
B:Sup{ .m(x)->{ .k(y)->x } }
"""));}
@Test void keptInheritedMethodGenericMustNotBeCapturedByNestedLiteralWrittenGeneric(){ok(List.of("""
F[T]:{ .k[X](y:X):T; }
Sup:{ .m[X](x:X):F[X]; }
B:Sup{ .m[X](x:X):F[X]->{ .k(y)->x } }
"""));}
@Test void keptInheritedMethodGenericMustNotBeShadowedByNestedLiteral(){fail("""
003| B:Sup{ .m(x)->{ .k(y)->x } }
   |        ---------~~~~~~~^--

While inspecting parameter "x" > method ".k(_)" (line 3) > method ".m(_)" (line 3)
Method ".k(_)" inside the object literal instance of "G" (line 3)
is implemented with an expression returning "imm X".
Parameter "x" has type "imm X" instead of a subtype of "_AX".

Name "_AX" stands for generic type parameter "X" of an inherited method, renamed because "X" already names a type or another generic type parameter.

Relevant code with inferred types:
B:Sup{.m[X](x:X):G->G{.k[_AX](y:_AX):_AX->x}}
""", List.of("""
G:{ .k[X](y:X):X; }
Sup:{ .m[X](x:X):G; }
B:Sup{ .m(x)->{ .k(y)->x } }
"""));}
@Test void freshMethodGenericMustNotCaptureKeptEnclosingGeneric(){ok(List.of("""
F[T]:{ .k[X](y:X):T; }
Sup:{ .m[_AX](x:_AX):F[_AX]; }
B:Sup{ .m(x)->{ .k(y)->x }; .q[X]:Sup->this }
"""));}
@Test void keptInheritedMethodGenericMustNotBeTypeNameInLiteral(){fail("""
002| A:{ .foo:base.Todo->{ ! -> this } }
   |     ------------------~~~~~^^^^--

While inspecting parameter "this" > method "!" (line 2) > method ".foo" (line 2)
Method "!" inside the object literal instance of "base.Todo" (line 2)
is implemented with an expression returning "A".
Parameter "this" has type "A" instead of a subtype of "_AR".

Name "_AR" stands for generic type parameter "R" of an inherited method, renamed because "R" already names a type or another generic type parameter.

Relevant code with inferred types:
A:{.foo:base.Todo->base.Todo{![_AR:**]:_AR->this}}
""", List.of("""
R:{}
A:{ .foo:base.Todo->{ ! -> this } }
"""));}
@Test void unnamedLiteralThisMisbinding_getsEnclosingLiteralHint(){fail("""
001| Outer: { #: Inner -> Inner: { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
   |                               -------------------~~~~^^^^

While inspecting method ".foo" (line 1) > method "#" (line 1)
This call to method ".bar" cannot typecheck.
Method ".bar" is not declared on type "Outer".
Parameter "this" has type "Outer".
Method ".bar" is declared in the object literal "Inner", which has no self name.
A self name is declared with a single quote, as "'rect" in the example below:
  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect
    .area: Nat -> width * height;
    .str: Str -> "area: "+(rect.area.str);
    .withWidth(width': Nat): Rectangle -> this#(width', height);
  }}

Available methods on type "Outer":
- #:Inner

Relevant code with inferred types:
this.bar
""", List.of("""
Outer: { #: Inner -> Inner: { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
"""));}
@Test void namedEnclosingLiteralThisMisbinding_getsEnclosingLiteralHint(){fail("""
001| Outer: { #: Inner -> Inner:{'self .foo: Innermost -> Innermost: { .a: base.Void -> this.bar; }; .bar: base.Void -> base.Void; } }
   |                                                                   -----------------~~~~^^^^

While inspecting method ".a" (line 1) > method ".foo" (line 1) > method "#" (line 1)
This call to method ".bar" cannot typecheck.
Method ".bar" is not declared on type "Outer".
Parameter "this" has type "Outer".
Method ".bar" is declared in the object literal "Inner", whose self name is "self".

Available methods on type "Outer":
- #:Inner

Relevant code with inferred types:
this.bar
""", List.of("""
Outer: { #: Inner -> Inner:{'self .foo: Innermost -> Innermost: { .a: base.Void -> this.bar; }; .bar: base.Void -> base.Void; } }
"""));}
@Test void anonEnclosingLiteralThisMisbinding_hintDoesNotShowFreshName(){fail("""
002| Outer:{ #: G -> { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
   |                   -------------------~~~~^^^^

While inspecting method ".foo" (line 2) > method "#" (line 2)
This call to method ".bar" cannot typecheck.
Method ".bar" is not declared on type "Outer".
Parameter "this" has type "Outer".
Method ".bar" is declared in the object literal instance of "G", which has no self name.
A self name is declared with a single quote, as "'rect" in the example below:
  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect
    .area: Nat -> width * height;
    .str: Str -> "area: "+(rect.area.str);
    .withWidth(width': Nat): Rectangle -> this#(width', height);
  }}

Available methods on type "Outer":
- #:G

Relevant code with inferred types:
this.bar
""", List.of("""
G:{ .foo: base.Void; .bar: base.Void; }
Outer:{ #: G -> { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
"""));}
@Test void anonReceiverTypeArgBounds_doesNotShowFreshName(){fail("""
002| Outer:{ #: G -> {'self .foo[X:imm]: base.Void -> base.Void; .bar: base.Void -> self.foo[mut Outer]; } }
   |         ----------------------------------------------------~~~~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^---

While inspecting method call ".foo" > method ".bar" (line 2) > method "#" (line 2)
The call to ".foo" is invalid.
Generic type argument 1 ("mut Outer") does not satisfy the bounds
for generic type parameter "X" in "G.foo".
Here "X" can only use capability "imm".

Relevant code with inferred types:
self.foo[imm,mut Outer]
""", List.of("""
G:{ .foo[X:imm]: base.Void; .bar: base.Void; }
Outer:{ #: G -> {'self .foo[X:imm]: base.Void -> base.Void; .bar: base.Void -> self.foo[mut Outer]; } }
"""));}
@Test void anonLiteralAsTypeArgument_doesNotShowFreshName(){fail("""
004| Outer:{ #: G -> {'self .bar -> base.Void; .v -> Boxes#(self) } }
   |         ----------------------------------~~~~~~^^^^^^^^^^^^--

While inspecting method call "#(_)" > method ".v" (line 4) > method "#" (line 4)
Method ".v" inside the object literal instance of "G" (line 4)
is implemented with an expression returning "Box[G]".
Method call "Boxes#(_)" has type "Box[G]" instead of a subtype of "base.Void".

Relevant code with inferred types:
Outer:{#:G->G{'self .bar:base.Void->base.Void;.v:base.Void->Boxes#[imm,G](self)}}
""", List.of("""
Box[E]:{ .get: E }
Boxes:{ #[E](e: E): Box[E] -> {.get -> e} }
G:{ .bar: base.Void; .v: base.Void; }
Outer:{ #: G -> {'self .bar -> base.Void; .v -> Boxes#(self) } }
"""));}
@Test void tsMiniFail(){fail("""
001| A:{.foo123:A->this.ba}
   |    -----------~~~~^^^

While inspecting method ".foo123" (line 1)
This call to method ".ba" cannot typecheck.
Method ".ba" is not declared on type "A".

Available methods on type "A":
- .foo123:A

Relevant code with inferred types:
this.ba
""", List.of("""
A:{.foo123:A->this.ba}
"""));}
@Test void emptyLiteralArgumentOfUndeclaredMethod(){fail("""
001| A:{ .m(x: B): B -> x.foo({}); }
   |     ---------------~^^^^~~~~

While inspecting method ".m(_)" (line 1)
This call to method ".foo(_)" cannot typecheck.
Method ".foo(_)" is not declared on type "B".
Type "B" does not have any methods.

Relevant code with inferred types:
x.foo({})
""", List.of("""
A:{ .m(x: B): B -> x.foo({}); }
B:{}
"""));}
@Test void typeNotWellKinded_genericInstantiationViolatesBounds(){fail("""
003| User:{ imm .m(a:imm A[mut B]):base.Void; }
   | --------------------^^^^^^^^--------------

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "imm".

Relevant code with inferred types:
User:{.m(a:A[mut B]):base.Void}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm A[mut B]):base.Void; }
"""));}

@Test void typeNotWellKinded_secondTypeArgViolatesBoundsInParamType(){fail("""
004| User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
   | --------------------^^^^^^^^^^^^^^--------------

While inspecting type declaration "User"
The type "A[B,mut C]" is invalid.
Generic type argument 2 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "A[_,_]".
Here "Y" can only use capabilities "iso" or "read".

Relevant code with inferred types:
User:{.m(a:A[B,mut C]):base.Void}
""", List.of("""
A[X:imm,Y:read,iso]:{}
B:{}
C:{}
User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
"""));}

@Test void typeNotWellKinded_nestedInnerGenericViolatesBounds(){fail("""
004| User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting type declaration "User"
The type "B[mut C]" is invalid.
Generic type argument 1 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "B[_]".
Here "Y" can only use capability "imm".

Relevant code with inferred types:
User:{.m(a:A[B[mut C]]):base.Void}
""", List.of("""
A[X:imm]:{}
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_literalSupertypeViolatesBounds(){fail("""
003| User:A[mut B]{ .foo(b:B):B->b;}
   | -----^^^^^^^^------------------

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm" or "mutH" or "readH".

Relevant code with inferred types:
User:A[mut B]{.foo(b:B):B->b}
""", List.of("""
A[X:imm,readH,mutH]:{}
B:{}
User:A[mut B]{ .foo(b:B):B->b;}
"""));}

@Test void typeNotWellKinded_methodReturnTypeViolatesBounds(){fail("""
003| User:{ imm .m(a:imm B):imm A[mut B]; }
   | ---------------------------^^^^^^^^---

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "imm".

Relevant code with inferred types:
User:{.m(a:B):A[mut B]}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm B):imm A[mut B]; }
"""));}

@Test void typeNotWellKinded_methodTypeArgViolatesBounds_simple(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting method call ".id(_)" > method ".m(_,_)" (line 3)
The call to ".id(_)" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capability "imm".

Relevant code with inferred types:
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgSecondParamViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
   |        -------------------------------------------^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".pair(_,_)" > method ".m(_,_,_)" (line 5)
The call to ".pair(_,_)" is invalid.
Generic type argument 2 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "A.pair(_,_)".
Here "Y" can only use capability "read".

Relevant code with inferred types:
a.pair[imm,B,mut C](b,c)
""", List.of("""

A:{ imm .pair[X:imm,Y:read](x:X,y:Y):base.Void->{} }
B:{}
C:{}
User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
"""));}

@Test void typeNotWellKinded_methodTypeArgNestedViolatesBounds(){fail("""
004| User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
   |        ----------------------------------------------~~~~~~^^^^^^^^~~~~

While inspecting method call ".use(_)" > method ".m(_,_,_)" (line 4)
The type "B[mut C]" is invalid.
Generic type argument 1 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "B[_]".
Here "Y" can only use capability "imm".

Relevant code with inferred types:
a.use[imm,B[mut C]](b)
""", List.of("""
A:{ imm .use[X:imm](x:X):base.Void->{} }
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
"""));}

@Test void typeNotWellKinded_literalHeaderUsesTypeParamViolatingBounds(){fail("""
002| User[Y:read]:A[Y]{}
   | -------------^^^^--

While inspecting type declaration "User[_]"
The type "A[Y]" is invalid.
Generic type argument 1 ("Y") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "imm".
But generic type argument "Y" can only use capability "read".

Relevant code with inferred types:
User[Y:read]:A[Y]{}
""", List.of("""
A[X:imm]:{}
User[Y:read]:A[Y]{}
"""));}

@Test void typeNotWellKinded_nestedTwiceInnerMostViolatesBounds(){fail("""
004| User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting type declaration "User"
The type "B[mut C]" is invalid.
Generic type argument 1 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "B[_]".
Here "Y" can only use capability "read".

Relevant code with inferred types:
User:{.m(x:A[B[mut C]]):base.Void}
""", List.of("""
A[X:imm]:{}
B[Y:read]:{}
C:{}
User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeWithMultipleBounds(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting method call ".id(_)" > method ".m(_,_)" (line 3)
The call to ".id(_)" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "imm" or "read".

Relevant code with inferred types:
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}


@Test void typeNotWellKinded_methodTypeArgOnTypeInfer(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
   |        -----------------------------------^^^^^^^

While inspecting method call ".id(_)" > method ".m(_,_)" (line 3)
The call to ".id(_)" is invalid.
Generic type argument 1 ("imm B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "mut" or "read".

Relevant code with inferred types:
a.id[imm,B](b)
""", List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeInfer2(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
   |        --------------------------------^^^^^^^

While inspecting method call ".id(_)" > method ".m(_,_)" (line 3)
The call to ".id(_)" is invalid.
Generic type argument 1 ("imm B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "iso" or "mut".

Relevant code with inferred types:
a.id[imm,B](b)
""", List.of("""
A:{ imm .id[X:mut,iso](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
"""));}

@Test void typeNotWellKinded_typeExpressionViolatesBounds(){fail("""
004|   .break(cell:imm Cell):base.Void ->
005|     Thaw[mut Cell].apply(cell).set(1);
   |     ^^^^^^^^^^^^^^

While inspecting object literal instance of "Thaw[mut Cell]" > method ".break(_)" (line 4)
The type "Thaw[mut Cell]" is invalid.
Generic type argument 1 ("mut Cell") does not satisfy the bounds
for generic type parameter "X" in "Thaw[_]".
Here "X" can only use capability "imm".
""", List.of("""
Cell:{ read .get:base.Nat; mut .set(value:base.Nat):base.Void; }
Thaw[X:imm]:{ .apply(x:imm X):X -> x; }
User:{
  .break(cell:imm Cell):base.Void ->
    Thaw[mut Cell].apply(cell).set(1);
}
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeInferFromRetType(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id[read B](b); }
"""));}
@Test void typeNotWellKinded_twistToPassInfer(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:mut B):read B->a.id[read B](b); }
"""));}


@Test void okViaPushToIso_methodImplementationDeadCode_readLiteralHasMutMethod(){ ok(List.of("""
B:{ mut .h:base.Void; }
User:{
  imm .m():read B->read BB:B{
    mut .h:base.Void->base.Void{};
  }
}
"""));}

@Test void okViaPushToIso_methodImplementationDeadCode_immLiteralHasMutMethod(){ ok(List.of("""
B:{ mut .h:base.Void; }
User:{
  imm .m():imm B->imm BB:B{
    mut .h:base.Void->base.Void{};
  }
}
"""));}

@Test void notAffineIso_usedDirectlyTwice_sameCall(){ fail("""
004| User:{ imm .bad(x:iso B):Unit->Use2#(x,x); }
   |        ------------------------------^~~-

While inspecting method ".bad(_)" (line 4)
Iso parameter "x" violates the single-use rule in method "User.bad(_)" (line 4).
It is used directly 2 times.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.

Relevant code with inferred types:
Use2#(x,x)
""", List.of("""
Unit:{}
B:{}
Use2:{ #(a:iso B,b:iso B):Unit->Unit{} }
User:{ imm .bad(x:iso B):Unit->Use2#(x,x); }
"""));}

@Test void notAffineIso_usedDirectlyAndCaptured_literalArg(){ fail("""
007|   imm .bad(xyz:iso B):Unit->Mix#(xyz, imm KK:K{ imm .k:Unit->UseImm#(xyz); });
   |   -------------------------------^^^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-----

While inspecting method ".bad(_)" (line 7)
Iso parameter "xyz" violates the single-use rule in method "User.bad(_)" (line 7).
It is used directly and also captured into object literals.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.

Relevant code with inferred types:
Mix#(xyz,KK:K{.k:Unit->UseImm#(xyz)})
""", List.of("""
Unit:{}
B:{}
UseImm:{ #(b:imm B):Unit->Unit{} }
K:{ imm .k:Unit; }
Mix:{ #(a:iso B,k:imm K):Unit->Unit{} }
User:{
  imm .bad(xyz:iso B):Unit->Mix#(xyz, imm KK:K{ imm .k:Unit->UseImm#(xyz); });
}
"""));}

@Test void notAffineIso_usedDirectlyAndCaptured_twice_twoLiterals(){ fail("""
008|   imm .bad(x:iso B):Unit->Mix2#(x,
   |                                 ^
009|     imm K1:K{ imm .k:Unit->UseImm#(x); },

While inspecting method ".bad(_)" (line 8)
Iso parameter "x" violates the single-use rule in method "User.bad(_)" (line 8).
It is used directly and also captured into object literals.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.

Relevant code with inferred types:
Mix2#(x,K1:K{.k:Unit->UseImm#(x)},K2:K{.k:Unit->UseImm#(x)})
""", List.of("""

Unit:{}
B:{}
UseImm:{ #(b:imm B):Unit->Unit{} }
K:{ imm .k:Unit; }
Mix2:{ #(a:iso B,k1:imm K,k2:imm K):Unit->Unit{} }
User:{
  imm .bad(x:iso B):Unit->Mix2#(x,
    imm K1:K{ imm .k:Unit->UseImm#(x); },
    imm K2:K{ imm .k:Unit->UseImm#(x); }
  );
}
"""));}
@Test void notAffineIso_implicitParameterUsedDirectlyTwice(){ fail("""
004| User:{ .bad:base.F[iso B,Unit]->{ Use2#(::,::) } }
   |                                   ------^^~~~-

While inspecting method "#(_)" (line 4) > method ".bad" (line 4)
Iso parameter "::" violates the single-use rule in method "read base.F[iso B,Unit]#(_)" (line 4).
It is used directly 2 times.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.

Relevant code with inferred types:
Use2#(::,::)
""", List.of("""
Unit:{}
B:{}
Use2:{ #(a:iso B,b:iso B):Unit->Unit{} }
User:{ .bad:base.F[iso B,Unit]->{ Use2#(::,::) } }
"""));}
@Test void notAffineIso_destructuredParameterUsedDirectlyTwice(){ fail("""
002| User:{ .bad({.a,.b}:iso B):B->a }
[###]
While inspecting method ".bad(_)" (line 2)
Iso parameter "{.a, .b}" violates the single-use rule in method "User.bad(_)" (line 2).
It is used directly 2 times.
An iso parameter can either be captured into object literals, where it is seen as "imm", or be used directly once.
[###]
""", List.of("""
B:{ .a:B->this; .b:B->this; }
User:{ .bad({.a,.b}:iso B):B->a }
"""));}

@Test void methodBodyWrongType_xWrongNominal_shortNames(){ fail("""
004|   imm .m(x:imm A):B->x;
   |   -------------------^

While inspecting parameter "x" > method ".m(_)" (line 4)
The body of method ".m(_)" of type declaration "User" is an expression returning "A".
Parameter "x" has type "A" instead of a subtype of "B".

Relevant code with inferred types:
User:{.m(x:A):B->x}
""", List.of("""
A:{}
B:{}
User:{
  imm .m(x:imm A):B->x;
}
"""));}

@Test void methodBodyWrongType_xWrongNominal_longNames_indent(){ fail("""
004|   imm .veryLongMethodName(veryVeryLongParamName:imm Alpha):Beta->
005|     veryVeryLongParamName;
   |     ^^^^^^^^^^^^^^^^^^^^^

While inspecting parameter "veryVeryLongParamName" > method ".veryLongMethodName(_)" (line 4)
The body of method ".veryLongMethodName(_)" of type declaration "User" is an expression returning "Alpha".
Parameter "veryVeryLongParamName" has type "Alpha" instead of a subtype of "Beta".

Relevant code with inferred types:
User:{.veryLongMethodName(veryVeryLongParamName:Alpha):Beta->veryVeryLongParamName}
""", List.of("""
Alpha:{}
Beta:{}
User:{
  imm .veryLongMethodName(veryVeryLongParamName:imm Alpha):Beta->
    veryVeryLongParamName;
}
"""));}

@Test void methodBodyWrongType_callWrongType_namedCallee(){ fail("""
005|   imm .m():B->MakeA#({  }    );
   |   ------------^^^^^^^^^^^^^^^^

While inspecting method call "#(_)" > method ".m" (line 5)
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "B".

Relevant code with inferred types:
User:{.m:B->MakeA#(base.Void)}
""", List.of("""
A:{}
B:{}
MakeA:{ #(u:base.Void):A->A{} }
User:{
  imm .m():B->MakeA#({  }    );
}
"""));}

@Test void methodBodyWrongType_callWrongType_rcOnly(){ fail("""
004|   imm .m():mut A->MakeA#({  }    );
   |   ----------------^^^^^^^^^^^^^^^^

While inspecting method call "#(_)" > method ".m" (line 4)
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "mut A".

Relevant code with inferred types:
User:{.m:mut A->MakeA#(base.Void)}
""", List.of("""
A:{}
MakeA:{ #(u:base.Void):A->A{} }
User:{
  imm .m():mut A->MakeA#({  }    );
}
"""));}

@Test void methodBodyWrongType_callWrongType_rcOnly_nested(){ fail("""
005|   imm .m():Get->mut Get{
006|     mut .get:mut A->MakeA#({});
   |     ----------------^^^^^^^^^^
007|   };

While inspecting method call "#(_)" > method ".get" (line 6) > method ".m" (line 5)
Method ".get" inside the object literal instance of "mut Get" (line 5)
is implemented with an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "mut A".

Relevant code with inferred types:
User:{.m:Get->mut Get{mut .get:mut A->MakeA#(base.Void)}}
""", List.of("""
A:{}
MakeA:{ #(u:base.Void):A->A{} }
Get:{ mut .get:mut A; }
User:{
  imm .m():Get->mut Get{
    mut .get:mut A->MakeA#({});
  };
}
"""));}

@Test void methodBodyWrongType_inferredContextShowsInferredGenericInstantiation(){fail("""
007|   imm .m():Car->Apply#(Person,{_->Foo});
   |   -----------------------------~~~^^^--

While inspecting object literal instance of "Foo" > method "#(_)" (line 7) > method ".m" (line 7)
Method "#(_)" inside the object literal instance of "F[Person,Car]" (line 7)
is implemented with an expression returning "Foo".
Object literal is of type "Foo" instead of a subtype of "Car".

Relevant code with inferred types:
User:{.m:Car->Apply#(Person,F[Person,Car]{#(Person):Car->Foo})}
""", List.of("""
Person:{}
Car:{}
Foo:{}
F[A:imm,B:imm]:{ #(a:imm A):B; }
Apply:{ #(p:imm Person, f:imm F[Person,Car]):Car->f#(p); }
User:{
  imm .m():Car->Apply#(Person,{_->Foo});
}
"""));}
@Test void methodBodyWrongType_callWrongType_nestedCall(){ fail("""
006|   imm .m():B->Wrap#(Mk#({}));
   |   ------------^^^^^^^^^^^^^^

While inspecting method call "#(_)" > method ".m" (line 6)
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "Wrap#(_)" has type "A" instead of a subtype of "B".

Relevant code with inferred types:
User:{.m:B->Wrap#(Mk#(base.Void))}
""", List.of("""
A:{}
B:{}
Mk:{ #(u:base.Void):A->A{} }
Wrap:{ #(a:A):A->a }
User:{
  imm .m():B->Wrap#(Mk#({}));
}
"""));}

@Test void methodBodyWrongType_literalWrongType_namedLiteral(){ fail("""
004|   imm .m():B->imm AA:A{};
   |   ----------------^^^^^^

While inspecting object literal "AA" > method ".m" (line 4)
The body of method ".m" of type declaration "User" is an expression returning "AA".
Object literal is of type "AA" instead of a subtype of "B".

Relevant code with inferred types:
User:{.m:B->AA:A{}}
""", List.of("""
A:{}
B:{}
User:{
  imm .m():B->imm AA:A{};
}
"""));}
@Test void methodBodyWrongType_xWeakenedCapability_dueToCapture(){fail("""
004|   read .m(loooooong:mut A):mut A->
005|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > method ".get" (line 5) > method ".m(_)" (line 4)
Method ".get" inside the object literal instance of "read Get" (line 5)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capturing changes the type of parameter "loooooong":
- "mut A" becomes "read A" inside the "read" method ".get" (line 5).

Relevant code with inferred types:
User:{read .m(loooooong:mut A):mut A->read Get{read .get:mut A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: mut A; }
User:{
  read .m(loooooong:mut A):mut A->
    read Get{ loooooong };
}
"""));}
@Test void methodBodyWrongType_xWeakenedCapability_dueToCapture2(){fail("""
004|   read .m(loooooong:mut A):read Get->
005|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > method ".get" (line 5) > method ".m(_)" (line 4)
Method ".get" inside the object literal instance of "read Get" (line 5)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capturing changes the type of parameter "loooooong":
- "mut A" becomes "read A" inside the "read" method ".get" (line 5).

Relevant code with inferred types:
User:{read .m(loooooong:mut A):read Get->read Get{read .get:iso A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: iso A; }
User:{
  read .m(loooooong:mut A):read Get->
    read Get{ loooooong };
}
"""));}
@Test void regressionBadError(){fail("""
004|   read .m(loooooong:mut A):mut A->
005|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > method ".get" (line 5) > method ".m(_)" (line 4)
Method ".get" inside the object literal instance of "read Get" (line 5)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capturing changes the type of parameter "loooooong":
- "mut A" becomes "read A" inside the "read" method ".get" (line 5).

Relevant code with inferred types:
User:{read .m(loooooong:mut A):mut A->read Get{read .get:iso A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: iso A; }
User:{
  read .m(loooooong:mut A):mut A->
    read Get{ loooooong };
}
"""));}

@Test void methodBodyWrongType_xWeakenedCapability_dueToCapture_chain(){fail("""
005|   read .m(loooooong:mut A):mut A->
006|     read Wrap{ mut Get{ loooooong } };
   |                ---------^^^^^^^^^--

While inspecting parameter "loooooong" > method ".get" (line 6) > method ".wrap" (line 6) > method ".m(_)" (line 5)
Method ".get" inside the object literal instance of "mut Get" (line 6)
is implemented with an expression returning "A".
Parameter "loooooong" has type "imm A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capturing changes the type of parameter "loooooong":
- "mut A" becomes "read A" inside the "read" method ".wrap" (line 6).
- "read A" becomes "imm A" inside the "imm" method ".get" (line 6).

Relevant code with inferred types:
User:{read .m(loooooong:mut A):mut A->read Wrap{read .wrap:Get->mut Get{.get:iso A->loooooong}}}
""", List.of("""
A:{}
Get:{ imm .get: iso A; }
Wrap:{ read .wrap: imm Get; }
User:{
  read .m(loooooong:mut A):mut A->
    read Wrap{ mut Get{ loooooong } };
}
"""));
}

@Test void drop_capFreeNamesTheLineOfTheObjectLiteralAndOfTheUse(){fail("""
003| Foo:{#(a:A):G->
004|   {
005|     a
   |     ^
006|   }

While inspecting parameter "a" > method "#" (line 5) > method "#(_)" (line 3)
Object literal instance of "G" (line 4) implements "base.CaptureFree".
Thus parameter "a" (line 5) cannot be captured in that object literal.
""", List.of("""
A:{}
G:base.CaptureFree{ #:A; }
Foo:{#(a:A):G->
  {
    a
  }
  }
"""));}
@Test void drop_capFree(){fail("""
003| Foo:{#(a:A):G->{a}}
   |      -----------^-

While inspecting parameter "a" > method "#" (line 3) > method "#(_)" (line 3)
Object literal instance of "G" (line 3) implements "base.CaptureFree".
Thus parameter "a" (line 3) cannot be captured in that object literal.
""", List.of("""
A:{}
G:base.CaptureFree{ #:A; }
Foo:{#(a:A):G->{a}}
""")); }


@Test void drop(){fail("""
007|   read .m(loooooong:mut A):mut A->Do2[mut A]#(
008|     Capture#({#():base.Void->Ignore#(loooooong)}),
   |               -----------------------^^^^^^^^^-
009|     loooooong
010|   );

While inspecting parameter "loooooong" > method "#" (line 8) > method ".m(_)" (line 7)
Parameter "loooooong" has type "mut A".
Parameter "loooooong" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "G" (line 8).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
A:{}
G:{ #(): base.Void; }
Ignore:{ #(x: read A): base.Void->{}; }
Capture:{#(g: G): base.Void->{}; }
Do2[X:imm,mut,read]: { #(v:base.Void, x:X):X->x; }
User:{
  read .m(loooooong:mut A):mut A->Do2[mut A]#(
    Capture#({#():base.Void->Ignore#(loooooong)}),
    loooooong
  );
}
"""));}

@Test void drop_hygienicMutH(){fail("""
007|   read .m(loooooong:mutH A):mutH A->Do2H[mutH A]#(
008|     Capture#({#():base.Void->Ignore#(loooooong)}),
   |               -----------------------^^^^^^^^^-
009|     loooooong
010|   );

While inspecting parameter "loooooong" > method "#" (line 8) > method ".m(_)" (line 7)
Parameter "loooooong" has type "mutH A".
The type of parameter "loooooong" is hygienic (readH or mutH)
and thus it cannot be captured in the object literal instance of "G" (line 8).
""", List.of("""
A:{}
G:{ #(): base.Void; }
Ignore:{ #(x: mutH A): base.Void->{}; }
Capture:{ #(g: G): base.Void->{}; }
Do2H[X:imm,mut,read,readH,mutH]: { #(v:base.Void, x:X):X->x; }
User:{
  read .m(loooooong:mutH A):mutH A->Do2H[mutH A]#(
    Capture#({#():base.Void->Ignore#(loooooong)}),
    loooooong
  );
}
""")); }

@Test void drop_hygienicMutH2(){fail("""
005|   read .m(loooooong:mutH A):imm G->
006|     {#():base.Void->IgnoreH#(loooooong)};
   |      ------------------------^^^^^^^^^-

While inspecting parameter "loooooong" > method "#" (line 6) > method ".m(_)" (line 5)
Parameter "loooooong" has type "mutH A".
The type of parameter "loooooong" is hygienic (readH or mutH)
and thus it cannot be captured in the object literal instance of "G" (line 6).
""", List.of("""
A:{}
G:{ #(): base.Void; }
IgnoreH:{ #(x: mutH A): base.Void->{}; }
User:{
  read .m(loooooong:mutH A):imm G->
    {#():base.Void->IgnoreH#(loooooong)};
}
""")); }
@Test void shouldPassViaInference(){ok(List.of("""
Bar:{}
Beer[X:imm,mut,read]:{ read .bar: Bar; }
Foo:{ read .m: Bar; }
User:{
  read .m[X:imm,mut,read](webeer:Beer[X]):read Foo->
    read Foo{ webeer.bar() };
}
""")); }

@Test void drop_ftv_notPropagatedIntoExplicitFoo(){failWf("""
005|       read Foo:{ read .m:Bar -> beer.bar() };
   |                                 ^^^^

While inspecting parameter "beer"
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> beer.bar() };
  }
""")); }
@Test void drop_ftv_typeVariableNotPropagatedIntoExplicitFoo(){failWf("""
004|       read Foo:{ read .m:Bar -> x };
   |                                 ^

While inspecting parameter "x"
Parameter "x" has type "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  User:{
    read .m[X:imm,mut,read](x:X):read Foo->
      read Foo:{ read .m:Bar -> x };
  }
"""));}
@Test void drop_ftv_notPropagatedTypeReachesInferredTypeArgument(){failWf("""
006|       read Foo:{ read .m:Bar -> Id#beer };
   |                                    ^^^^

While inspecting parameter "beer"
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  Id:{ #[Y:imm,mut,read](y:Y):Bar -> Bar }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> Id#beer };
  }
"""));}
@Test void drop_ftv_notPropagatedTypeReachesNestedLiteral(){failWf("""
007|       read Foo:{ read .m:Bar -> Do#{ beer.bar } };
   |                                      ^^^^

While inspecting parameter "beer"
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  Run:{ read #: Bar }
  Do:{ #(r: read Run): Bar -> Bar }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> Do#{ beer.bar } };
  }
"""));}
@Test void drop_ftv_notPropagatedIntoFooDeclaringOther(){failWf("""
[###]
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares "Z".
Funnel "X" into "Foo" by writing "Foo[Z:..,X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  User:{
    read .m[X:imm,mut,read,Z](beer:Beer[X]):read Foo[Z]->
      read Foo[Z]:{ read .m:Bar -> beer.bar() };
  }
"""));}

@Test void drop_hygienicsAllowedByTypeParam(){fail("""
002|   read .m[X:imm,mut,read,readH,mutH](beer:X):G[X]->
003|     G[X:imm,mut,read,readH,mutH]:{ read .get: X->beer; }
   |                                    --------------^^^^

While inspecting parameter "beer" > method ".get" (line 3) > method ".m(_)" (line 2)
Parameter "beer" has type "X".
The type of parameter "beer" can be instantiated with a hygienic capability (readH or mutH)
and thus it cannot be captured in the object literal "G[_]" (line 3).
""", List.of("""
User:{
  read .m[X:imm,mut,read,readH,mutH](beer:X):G[X]->
    G[X:imm,mut,read,readH,mutH]:{ read .get: X->beer; }
}
""")); }

@Test void receiverIsTypeParamDeepInsideCalls(){fail("""
002| User:{ .m[X:*](x: X): X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
   |        ----------------------------------------^~~~~-----

While inspecting method ".m(_)" (line 2)
This call to method ".foo" cannot typecheck.
The receiver has type "X", where "X" is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

Relevant code with inferred types:
Id#[imm,X](Id#[imm,X](Id#[imm,X](Id#[imm,X](Id#[imm,X](x.foo)))))
""", List.of("""
Id:{ #[T:*](t: T): T -> t }
User:{ .m[X:*](x: X): X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
"""));}
@Test void receiverIsReadTypeParamDeepInsideCalls(){fail("""
004| User:Sup[Box[User]]{ .m[X:*](x: read X): read X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
   |                      --------------------------------------------------^~~~~-----

While inspecting method ".m(_)" (line 4)
This call to method ".foo" cannot typecheck.
The receiver has type "read X", where "X" is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

Relevant code with inferred types:
Id#[imm,read X](Id#[imm,read X](Id#[imm,read X](Id#[imm,read X](Id#[imm,read X](x.foo)))))
""", List.of("""
Id:{ #[T:*](t: T): T -> t }
Box[T:*]:{}
Sup[T:*]:{}
User:Sup[Box[User]]{ .m[X:*](x: read X): read X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
"""));}
@Test void receiverIsReadImmTypeParamDeepInsideCalls(){fail("""
002| User:{ .m[X:*](x: read/imm X): read/imm X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
   |        ----------------------------------------------------------^~~~~-----

While inspecting method ".m(_)" (line 2)
This call to method ".foo" cannot typecheck.
The receiver has type "read/imm X", where "X" is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

Relevant code with inferred types:
Id#[imm,read/imm X](Id#[imm,read/imm X](Id#[imm,read/imm X](Id#[imm,read/imm X](Id#[imm,read/imm X](x.foo)))))
""", List.of("""
Id:{ #[T:*](t: T): T -> t }
User:{ .m[X:*](x: read/imm X): read/imm X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
"""));}
@Test void inferredTypeArgumentWithAnUnknownPartAndATypeParameter(){ok(List.of("""
Pair[A:*,B:*]:{}
Mk:{ #[A:*,B:*](a: A): Pair[A,B] -> {} }
Ig:{ #[T:*](t: T): base.Void -> base.Void }
User:{ .m[X:*](x: X): base.Void -> Ig#(Mk#(x)) }
"""));}
@Test void receiverIsTypeParam(){fail("""
002|   .m[X:**](x:X):X->x.foo;
   |   -----------------^~~~~

While inspecting method ".m(_)" (line 2)
This call to method ".foo" cannot typecheck.
The receiver has type "X", where "X" is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

Relevant code with inferred types:
User:{.m[X:**](x:X):X->x.foo}
""", List.of("""
User:{
  .m[X:**](x:X):X->x.foo;
}
""")); }
//-----------
@Test void methodOverrideSignatureMismatchGenericBounds(){ failExt("""
In file: [###].fear

003| Current:Parent2{ imm .id[X:imm,read](x:imm X):base.Void; }
   |                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Current"
Invalid method signature for "Current.id(_)".
The method ".id(_)" declares different capability bounds than the supertypes for generic type parameter 1.
Local declaration: "X:imm,read".
Capability bounds in the supertypes: "imm".
Generic type parameter names may differ from the supertypes; only the position matters.
Error 7 WellFormedness
""", List.of("""
P:{}
Parent2:{ imm .id[X:imm](x:imm X):base.Void; }
Current:Parent2{ imm .id[X:imm,read](x:imm X):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchGenericBoundsArity(){ failExt("""
In file: [###].fear

003| Sub:Sup{ imm .f[X:imm,Y:imm](x:imm X):base.Void; }
   |          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Sub"
Invalid method signature for "Sub.f(_)".
The method ".f(_)" declares 2 generic type parameters, but supertypes declare 1.
Error 7 WellFormedness
""", List.of("""
P:{}
Sup:{ imm .f[X:imm](x:imm X):base.Void; }
Sub:Sup{ imm .f[X:imm,Y:imm](x:imm X):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchContravariance(){ fail("""
004| Current:Parent{ imm .g(x:imm P):base.Void; }
   | ----------------^^^^^^^^^^^^^^^^^^^^^^^^^---

While inspecting type declaration "Current"
Invalid method signature for "Current.g(_)".
The method ".g(_)" accepts parameter 1 of type "imm P".
But "Parent.g(_)" requires "read P".
An overriding method can refine the types of its parameters and result, but not their capabilities.

Relevant code with inferred types:
Current:Parent{.g(x:P):base.Void}
""", List.of("""

P:{}
Parent:{ imm .g(x:read P):base.Void; }
Current:Parent{ imm .g(x:imm P):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchCovariance(){ fail("""
003| Sub:Sup{ imm .h():read P; }
   | ---------^^^^^^^^^^^^^^^---

While inspecting type declaration "Sub"
Invalid method signature for "Sub.h".
The method ".h" returns type "read P".
But "Sup.h" returns type "imm P".
An overriding method can refine the types of its parameters and result, but not their capabilities.

Relevant code with inferred types:
Sub:Sup{.h:read P}
""", List.of("""
P:{}
Sup:{ imm .h():imm P; }
Sub:Sup{ imm .h():read P; }
""")); }

@Test void callableMethodStillAbstract_missingRequiredMethod_anonLiteral(){ fail("""
006|   imm .m():Sup->Sup{ imm .h:base.Void->base.Void{} }
   |   --------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Sup" > method ".m" (line 6)
This object literal is missing a required method.
Missing: "imm .k".
Required by: "Sup".
Add an implementation for ".k" inside the object literal.

Relevant code with inferred types:
Sup{.h:base.Void->base.Void}
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Sup{ imm .h:base.Void->base.Void{} }
}
"""));}

@Test void callableMethodStillAbstract_missingRequiredMethod_namedLiteral(){ fail("""
006|   imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{} }
   |   --------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "Bad" > method ".m" (line 6)
This object literal is missing a required method.
Missing: "imm .k".
Required by: "Sup".
Add an implementation for ".k" inside the object literal.

Relevant code with inferred types:
Bad:Sup{.h:base.Void->base.Void}
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{} }
}
"""));}


@Test void methodNotDeclared_noSuchName_typeHasNoMethods(){fail("""
003|   read .m(e:Empty):base.Void->
004|     e.nope();
   |     -^^^^^--

While inspecting method ".m(_)" (line 3)
This call to method ".nope" cannot typecheck.
Method ".nope" is not declared on type "Empty".
Type "Empty" does not have any methods.

Relevant code with inferred types:
e.nope
""", List.of("""
Empty:{}
User:{
  read .m(e:Empty):base.Void->
    e.nope();
}
""")); }

@Test void methodNotDeclared_noSuchName_didYouMean(){fail("""
007|   read .m(o:Ops):base.Void->
008|     read Runner{ o.sise() };
   |                  -^^^^^--

While inspecting method ".run" (line 8) > method ".m(_)" (line 7)
This call to method ".sise" cannot typecheck.
Method ".sise" is not declared on type "Ops".
Did you mean ".size" ?

Available methods on type "Ops":
- read .sign:base.Void
- read .size:base.Void

Relevant code with inferred types:
o.sise
""", List.of("""
Ops:{
  read .size: base.Void->{};
  read .sign: base.Void->{};
}
Runner:{ read .run: base.Void; }
User:{
  read .m(o:Ops):base.Void->
    read Runner{ o.sise() };
}
""")); }
@Test void methodNotDeclared_noSuchName_listAvailable(){fail("""
007|   read .m(o:Ops):base.Void->
008|     o.xyzzy();
   |     -^^^^^^--

While inspecting method ".m(_)" (line 7)
This call to method ".xyzzy" cannot typecheck.
Method ".xyzzy" is not declared on type "Ops".

Available methods on type "Ops":
- read .alpha:base.Void
- read .beta:base.Void
- read .gamma:base.Void

Relevant code with inferred types:
o.xyzzy
""", List.of("""
Ops:{
  read .alpha: base.Void->{};
  read .beta: base.Void->{};
  read .gamma: base.Void->{};
}
User:{
  read .m(o:Ops):base.Void->
    o.xyzzy();
}
""")); }

@Test void methodNotDeclared_noSuchName_listAvailable_useVoid(){fail("""
008|   read .m(o:Ops):Woid->
009|     o.xyzzy();
   |     -^^^^^^--

While inspecting method ".m(_)" (line 8)
This call to method ".xyzzy" cannot typecheck.
Method ".xyzzy" is not declared on type "Ops".

Available methods on type "Ops":
- read .alpha:Woid
- read .beta:Woid
- read .gamma:Woid

Relevant code with inferred types:
o.xyzzy
""", List.of("""
use base.Void as Woid;
Ops:{
  read .alpha: Woid->{};
  read .beta:  Woid->{};
  read .gamma: Woid->{};
}
User:{
  read .m(o:Ops):Woid->
    o.xyzzy();
}
""")); }


@Test void methodNotDeclared_wrongArity_listsAvailableArities(){fail("""
007|   read .m(m:Mixer, a:A):A->
008|     m.mix(a, a, a);
   |     -^^^^---------

While inspecting method ".m(_,_)" (line 7)
This call to method ".mix(_,_,_)" cannot typecheck.
There are methods ".mix(_)" and ".mix(_,_)" on type "Mixer",
but with a different number of arguments.
This call supplies 3, but available methods take 1 or 2.

Relevant code with inferred types:
m.mix(a,a,a)
""", List.of("""
A:{}
Mixer:{
  read .mix(x:A):A->x;
  read .mix(x:A, y:A):A->x;
}
User:{
  read .m(m:Mixer, a:A):A->
    m.mix(a, a, a);
}
""")); }

@Test void methodNotDeclared_wrongArity_listsAritiesInNumericOrder(){fail("""
007|   read .m(m:Mixer, a:A):A->
008|     m.mix(a);
   |     -^^^^---

While inspecting method ".m(_,_)" (line 7)
This call to method ".mix(_)" cannot typecheck.
There are methods ".mix(_,_)" and ".mix(_,_,_,_,_,_,_,_,_,_)" on type "Mixer",
but with a different number of arguments.
This call supplies 1, but available methods take 2 or 10.

Relevant code with inferred types:
m.mix(a)
""", List.of("""
A:{}
Mixer:{
  read .mix(x:A, y:A):A->x;
  read .mix(x1:A, x2:A, x3:A, x4:A, x5:A, x6:A, x7:A, x8:A, x9:A, x10:A):A->x1;
}
User:{
  read .m(m:Mixer, a:A):A->
    m.mix(a);
}
""")); }
@Test void methodNotDeclared_wrongReceiverRc_mutNeedsMutButOnlyReadExists(){fail("""
006|   mut .m(z:mut Z, a:A):A->
007|     z.zap[mut](a);
   |     -^^^^--------

While inspecting method ".m(_,_)" (line 6)
This call to method ".zap(_)" cannot typecheck.
".zap(_)" exists on type "Z", but not with the requested capability.
This call requires a method with capability "mut".
Available capabilities for this method: "read".

Relevant code with inferred types:
z.zap[mut](a)
""", List.of("""
A:{}
Z:{
  read .zap(x:A):A->x;
}
User:{
  mut .m(z:mut Z, a:A):A->
    z.zap[mut](a);
}
""")); }
@Test void methodNotDeclared_wrongReceiverRc_onObjectLiteralInstance(){fail("""
002| U:{ .u: base.Void -> mut A{ read .m: base.Void -> base.Void; mut .k: base.Void -> base.Void }.k[read] }
   |     -----------------~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^^~~~~~~

While inspecting method ".u" (line 2)
This call to method ".k" cannot typecheck.
".k" exists on object literal instance of "A", but not with the requested capability.
This call requires a method with capability "read".
Available capabilities for this method: "mut".

Relevant code with inferred types:
mut A{read .m:base.Void->base.Void;mut .k:base.Void->base.Void}.k[read]
""", List.of("""
A:{ read .m: base.Void }
U:{ .u: base.Void -> mut A{ read .m: base.Void -> base.Void; mut .k: base.Void -> base.Void }.k[read] }
""")); }
@Test void methodNotDeclared_wrongReceiverRc_twoOtherCapabilitiesExist(){fail("""
002| User:{ #(a:read A):A->a.m[read] }
   |        ---------------~^^~~~~~~

While inspecting method "#(_)" (line 2)
This call to method ".m" cannot typecheck.
".m" exists on type "A", but not with the requested capability.
This call requires a method with capability "read".
Available capabilities for this method: "imm" and "mut".

Relevant code with inferred types:
a.m[read]
""", List.of("""
A:{ mut .m:A; imm .m:A; }
User:{ #(a:read A):A->a.m[read] }
""")); }
@Test void methodTArgsArityError_oneLessThanNeeded(){fail("""
007|   read .m(p:Pairer,a:mut A,b:mut B):mut A->
008|     p.pair[mut A](a,b);
   |     -^^^^^------------

While inspecting method ".m(_,_,_)" (line 7)
This call to method "read Pairer.pair(_,_)" cannot typecheck.
Wrong number of generic type arguments for ".pair(_,_)".
Method ".pair(_,_)" declares 2 generic type parameters.
Declared generic type parameters: "X", "Y".
This call provides 1 generic type argument.

Relevant code with inferred types:
p.pair[read,mut A](a,b)
""", List.of("""
A:{}
B:{}
Pairer:{
  read .pair[X:imm,mut,read,Y:imm,mut,read](x:X,y:Y):X->x;
}
User:{
  read .m(p:Pairer,a:mut A,b:mut B):mut A->
    p.pair[mut A](a,b);
}
"""));}

@Test void methodTArgsArityError_noneDeclared(){fail("""
007|   read .m(i:Id,a:mut A):mut A->
008|     i.id[mut A](a);
   |     -^^^----------

While inspecting method ".m(_,_)" (line 7)
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
Method ".id(_)" declares no generic type parameters.
This call provides 1 generic type argument.

Relevant code with inferred types:
i.id[read,mut A](a)
""", List.of("""

A:{}
Id:{
  read .id(x:mut A):mut A->x;
}
User:{
  read .m(i:Id,a:mut A):mut A->
    i.id[mut A](a);
}
"""));}

@Test void methodTArgsArityError_twoMoreThanNeeded(){fail("""
009|   read .m(i:Id,a:mut A):mut A->
010|     i.id[mut A,mut B,mut C](a);
   |     -^^^----------------------

While inspecting method ".m(_,_)" (line 9)
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
Method ".id(_)" declares 1 generic type parameter.
Declared generic type parameters: "X".
This call provides 3 generic type arguments.

Relevant code with inferred types:
i.id[read,mut A,mut B,mut C](a)
""", List.of("""

A:{}
B:{}
C:{}
Id:{
  read .id[X:imm,mut,read](x:X):X->x;
}
User:{
  read .m(i:Id,a:mut A):mut A->
    i.id[mut A,mut B,mut C](a);
}
"""));}

@Test void rcvBlocksCall(){fail("""
004|   read .m(a:A):A->
005|     this.zap(a);
   |     ^^^^-------

While inspecting method ".m(_)" (line 4)
This call to method "mut User.zap(_)" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".
The capability of the methods changes the type of parameter "this":
- "mut User" becomes "read User" inside the "read" method ".m(_)" (line 4).

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.zap[mut](a)
""", List.of("""
A:{}
User:{
  mut .zap(x:A):A->x;
  read .m(a:A):A->
    this.zap(a);
}
""")); }
@Test void operatorArgMismatch_getsNoPrecedenceHint(){fail("""
005|   .go:Plus->this + this.other;
   |   ----------~~~~~~~^^^^------

While inspecting method ".go" (line 5)
This call to method "Plus+(_)" cannot typecheck.
Argument 1 has type "Plus".
That is not a subtype of "A" (the type required by the method signature).
Fearless has no operator precedence, so an expression like "a.get + b.get" parses as "(a.get + b).get", not "a.get + (b.get)". If this argument needed a method applied to it first, wrap it in parentheses.

Relevant code with inferred types:
this + this
""", List.of("""
A:{}
Plus:{
  +(x:A):Plus->this;
  .other:A->A{};
  .go:Plus->this + this.other;
}
"""));}
@Test void aValueWhereALambdaIsExpectedGetsTheCurlyBracesHint(){fail("""
001| use base.Nat as Nat; A:{ #: Nat -> base.Block#.return 5 }
   |                          ----------~~~~~~~~~~~~~~~~~~~^

While inspecting method "#" (line 1)
This call to method "mut base.Block[_].return(_)" cannot typecheck.
Argument 1 has type "Nat".
That is not a subtype of "mut base.ReturnStmt[Nat]" (the type required by the method signature).
Write the argument inside curly braces: the curly braces make an object literal instance of "mut base.ReturnStmt[Nat]", whose single method returns the argument.

Relevant code with inferred types:
base.Block#[imm,Nat].return[mut](5)
""", List.of("""
use base.Nat as Nat; A:{ #: Nat -> base.Block#.return 5 }
"""));}
@Test void aMutParameterWhereAnImmLambdaIsExpectedGetsNoCurlyBracesHint(){fail("""
003| U:{ .take(g: Get): B -> B; .m(x: mut B): B -> this.take(x) }
   |                            -------------------~~~~~~~~~~^~

While inspecting method ".m(_)" (line 3)
This call to method "U.take(_)" cannot typecheck.
Argument 1 has type "B".
That is not a subtype of "Get" (the type required by the method signature).

Relevant code with inferred types:
this.take(x)
""", List.of("""
B:{}
Get:{ .get: mut B }
U:{ .take(g: Get): B -> B; .m(x: mut B): B -> this.take(x) }
"""));}
@Test void anIsoParameterWhereAMutLambdaIsExpectedGetsNoCurlyBracesHint(){fail("""
003| U:{ .take(g: mut Get): B -> B; .m(x: iso B): B -> this.take(x) }
   |                                -------------------~~~~~~~~~~^~

While inspecting method ".m(_)" (line 3)
This call to method "U.take(_)" cannot typecheck.
Argument 1 has type "B".
That is not a subtype of "mut Get" (the type required by the method signature).

Relevant code with inferred types:
this.take(x)
""", List.of("""
B:{}
Get:{ mut .get: mut B }
U:{ .take(g: mut Get): B -> B; .m(x: iso B): B -> this.take(x) }
"""));}
@Test void operatorArgMismatchNotFollowedByACallGetsNoPrecedenceHint(){fail("""
004|   .go:Plus->this + this;
   |   ----------~~~~~~~^^^^

While inspecting method ".go" (line 4)
This call to method "Plus+(_)" cannot typecheck.
Argument 1 has type "Plus".
That is not a subtype of "A" (the type required by the method signature).

Relevant code with inferred types:
this + this
""", List.of("""
A:{}
Plus:{
  +(x:A):Plus->this;
  .go:Plus->this + this;
}
"""));}
@Test void hopelessArg_wrongNominal_suppressesPromotionsAndReason(){fail("""
005|   .f(aaaa:mut B):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~~~^^^^^^^^^^^^^~

While inspecting method ".foo" (line 5) > method ".f(_)" (line 5)
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "B".
That is not a subtype of "mut A" (the type required by the method signature).

Relevant code with inferred types:
Need#(AsRead#(aaaa))
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read B):read B->x }
A:{
  .f(aaaa:mut B):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}
@Test void hopelessArg_wrongNominal_mutHReceiver_showsDeclaredType(){fail("""
005|   .f(n:mutH Need, b:B):B->n#b
   |   ------------------------~~^

While inspecting method ".f(_,_)" (line 5)
This call to method "mut Need#(_)" cannot typecheck.
Argument 1 has type "B".
That is not a subtype of "mut A" (the type required by the method signature).

Relevant code with inferred types:
n#[mut](b)
""", List.of("""
A:{}
B:{}
Need:{ mut #(a:mut A):B->B }
User:{
  .f(n:mutH Need, b:B):B->n#b
}
"""));}

@Test void hopelessArg_calls_pArgHasType_baselineConsistent(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~~~^^^^^^^^^^^^^~

While inspecting method ".foo" (line 5) > method ".f(_)" (line 5)
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
Method call "AsRead#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A" (As declared)
- "iso A" (Strengthen result)

Relevant code with inferred types:
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa))}}
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}

@Test void noVar2Fail_viewpointAdaptation_reasonShown(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,mut A](aaaa);}
   |                                    -------------~~~~~~~~~~~~~~~~~^^^^~

While inspecting method ".foo" (line 5) > method ".f(_)" (line 5)
This call to method "Skip#(_)" cannot typecheck.
Argument 1 has type "read A".
Parameter "aaaa" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capturing changes the type of parameter "aaaa":
- "mut A" becomes "read A" inside the "read" method ".foo" (line 5).

Type required by each promotion:
- "mut A" (As declared)
- "iso A" (Strengthen result)

Relevant code with inferred types:
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,mut A](aaaa)}}
""", List.of("""

Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,mut A](aaaa);}
}
"""));}

@Test void deepCall_usingRCfiltering(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}
}
"""));}

@Test void argFromGenericCall_boundForcesRead_inferenceHintBadBounds(){fail("""
006|   .f(aaaa:mut A):B->
007|     Need#(IdRO#(aaaa));
   |           ^^^^^^^^^^^

While inspecting method call "#(_)" > method ".f(_)" (line 6)
The call to "#(_)" is invalid.
Generic type argument 1 ("mut A") does not satisfy the bounds
for generic type parameter "X" in "IdRO#(_)".
Here "X" can only use capabilities "imm" or "read".

Relevant code with inferred types:
IdRO#[imm,mut A](aaaa)
""", List.of("""

B:{}
Need:{ #(a:mut A):B->B{} }
IdRO:{ #[X:imm,read](x:X):X->x }
A:{
  .f(aaaa:mut A):B->
    Need#(IdRO#(aaaa));
}
"""));}

@Test void argFromGenericCall_boundForcesRead_inferenceHint(){fail("""
005|   .f(aaaa:mut A):B->
006|     Need#(IdRO#[read A](aaaa));
   |     ------^^^^^^^^^^^^^^^^^^^-

While inspecting method ".f(_)" (line 5)
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
Method call "IdRO#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A" (As declared)
- "iso A" (Strengthen result)

Relevant code with inferred types:
A:{.f(aaaa:mut A):B->Need#(IdRO#[imm,read A](aaaa))}
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
IdRO:{ #[X:imm,read](x:X):X->x }
A:{
  .f(aaaa:mut A):B->
    Need#(IdRO#[read A](aaaa));
}
"""));}

@Test void argFromObjectLiteral_defaultImm_hintToAnnotate(){fail("""
005|   .f:B->
006|     Need#(read A{});
   |     ------^^^^^^^^-

While inspecting method ".f" (line 5)
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
Object literal is of type "read A" instead of a subtype of "mut A".
Write "mut A" if you need a "mut" object literal.

Type required by each promotion:
- "mut A" (As declared)
- "iso A" (Strengthen result)

Relevant code with inferred types:
User:{.f:B->Need#(read A)}
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
A:{ mut .foo:A}
User:{
  .f:B->
    Need#(read A{});
}
"""));}

@Test void promotionsDisagree_mergesIdenticalBlocks_readH_mutH(){fail("""
003|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^~~~~~

While inspecting method ".caller(_,_)" (line 3)
This call to method "A.f(_,_)" cannot typecheck.
Arguments 1 and 2 need different promotions, but a call uses one promotion for all its arguments.
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
  Argument 1 fails with: Allow mutH argument 2.
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.
  Argument 2 fails with: Allow readH arguments, Allow mutH argument 1.
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Relevant code with inferred types:
this.f(x,y)
""", List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void promotionsDisagree_dontOverMergeAcrossDifferentArgs_mutH_mutH(){fail("""
003|   .caller(x:mutH A, y:mutH A):A->this.f(x,y);
   |   -------------------------------~~~~^^~~~~~

While inspecting method ".caller(_,_)" (line 3)
This call to method "A.f(_,_)" cannot typecheck.
Arguments 1 and 2 need different promotions, but a call uses one promotion for all its arguments.
- Argument 1 has type "mutH A" and is compatible with: Allow mutH argument 1.
  Argument 1 fails with: Allow mutH argument 2.
  Parameter "x" has type "mutH A" instead of a subtype of "iso A".
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.
  Argument 2 fails with: Allow mutH argument 1.
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Relevant code with inferred types:
this.f(x,y)
""", List.of("""
A:{
  .f(a:mut A, b:mut A):A->this;
  .caller(x:mutH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Test void tsOkIndirectFail1(){fail("""
001| A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
   |                            --------~~~~^^^^^^^

While inspecting method ".bar" (line 1)
This call to method ".foO123" cannot typecheck.
Method ".foO123" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-     .bar:A
- mut .bob(A):A
-     .foo123:A

Relevant code with inferred types:
this.foO123
""", List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
"""));}

@Test void tsOkIndirectFail2(){fail("""
001| A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
   |                            --------~~~~^^^^^^

While inspecting method ".bar" (line 1)
This call to method ".foo23" cannot typecheck.
Method ".foo23" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
- .bar:A
- .foo123:A

Relevant code with inferred types:
this.foo23
""", List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
"""));}

@Test void tsOkIndirectFail3(){fail("""
001| A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
   |                            --------~~~~^^^^^^^^

While inspecting method ".bar" (line 1)
This call to method ".foo1123" cannot typecheck.
Method ".foo1123" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
- .bar:A
- .foo123:A

Relevant code with inferred types:
this.foo1123
""", List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
"""));}

@Test void tsOkIndirectFail4(){fail("""
003|   .bar:A->this.foo123(this);
   |   --------~~~~^^^^^^^~~~~~~

While inspecting method ".bar" (line 3)
This call to method ".foo123(_)" cannot typecheck.
There are methods ".foo123" and ".foo123(_,_,_)" on type "A",
but with a different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Relevant code with inferred types:
this.foo123(this)
""", List.of("""
A:{
  .foo123:A->this.foo123;
  .bar:A->this.foo123(this);
  .foo123(A,A,A):A->this.foo123;
  }
"""));}

@Test void tsOkIndirectFail4spaces(){fail("""
003|   .bar:A->this.foo123(this      );
   |   --------~~~~^^^^^^^~~~~~~~~~~~~

While inspecting method ".bar" (line 3)
This call to method ".foo123(_)" cannot typecheck.
There are methods ".foo123" and ".foo123(_,_,_)" on type "A",
but with a different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Relevant code with inferred types:
this.foo123(this)
""", List.of("""
A:{
  .foo123:A->this.foo123;
  .bar:A->this.foo123(this      );
  .foo123(A,A,A):A->this.foo123;
  }
"""));}
@Test void tsOkIndirectFail5(){fail("""
001| A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
   |                            ------------^^^^~~~~~~~

While inspecting method ".bar" (line 1)
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "mut".
This call requires a receiver with capability "imm".

Relevant code with inferred types:
this.foo123
""", List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail6a(){fail("""
001| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                            -------------^^^^~~~~~~~

While inspecting method ".bar" (line 1)
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".bar" (line 1).

Relevant code with inferred types:
this.foo123
""", List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Test void tsOkIndirectFail6b(){fail("""
001| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                            -------------^^^^~~~~~~~~~~~~

While inspecting method ".bar" (line 1)
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".bar" (line 1).

Relevant code with inferred types:
this.foo123
""", List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}
@Test void tsOkIndirectFail6c(){fail("""
001| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
   |                            -------------~~~~^^^^^^^~~~~~~

While inspecting method ".bar" (line 1)
This call to method ".foo123" cannot typecheck.
".foo123" exists on type "A", but not with the requested capability.
This call requires a method with capability "read".
Available capabilities for this method: "imm".

Relevant code with inferred types:
this.foo123[read]
""", List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
"""));}
@Test void implicitRcIsInferredInNestedLiteral(){ok(List.of("""
Counter:{ mut .inc: mut Counter; mut .inc2: mut Counter }
Make:{ #: mut Counter -> mut Counter{'self
  mut .inc: mut Counter -> self;
  mut .inc2: mut Counter -> self.inc.inc;
  } }
"""));}

@Test void tsOkIndirectFail7(){fail("""
001| A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
   |                                ------------^^^^~~~~~~~

While inspecting method ".bar" (line 1)
This call to method "mut A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "imm A" inside the "imm" method ".bar" (line 1).

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.foo123[mut]
""", List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail8(){fail("""
001| A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                            -------------^^^^~~~~~~~~~~~~

While inspecting method ".bar" (line 1)
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".bar" (line 1).

Relevant code with inferred types:
this.foo123
""", List.of("""
A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}

@Test void tsOkIndirectInferredAsRead(){ok(List.of("""
A:{mut .foo123:A->this.foo123; read .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail10(){fail("""
006|   read .bar:A->
007|     this.foo123[mut];
   |     ^^^^------------

While inspecting method ".bar" (line 6)
This call to method "mut A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".
The capability of the methods changes the type of parameter "this":
- "mut A" becomes "read A" inside the "read" method ".bar" (line 6).

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
this.foo123[mut]
""", List.of("""
A:{
  mut .foo123:A->
    this.foo123;
  imm .foo123:A->
    this.foo123;
  read .bar:A->
    this.foo123[mut];
  }
"""));}
@Test void baseTypeError(){fail("""
001| A:{ .bar(b:B):A->b; }
   |     -------------^

While inspecting parameter "b" > method ".bar(_)" (line 1)
The body of method ".bar(_)" of type declaration "A" is an expression returning "B".
Parameter "b" has type "B" instead of a subtype of "A".

Relevant code with inferred types:
A:{.bar(b:B):A->b}
""", List.of("""
A:{ .bar(b:B):A->b; }
B:{ }
"""));}
@Test void uncallableMethodOk(){ok(List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{}; }
"""));}
@Test void uncallableMethodFail(){fail("""
002| A:{ mut .baz(b: mut B):read B-> { .bar->b}; }
   |     ----------------------------~~^^^^^^^~

While inspecting object literal instance of "read B" > method ".baz(_)" (line 2)
The method "mut B.bar" is dead code.
The object literal instance of "B" is "read", so it will never be seen as "mut".
But it implements method "mut .bar", which requires a "mut" receiver.

Relevant code with inferred types:
read B{mut .bar:mut B->b}
""", List.of("""
B:{ mut .bar:mut B }
A:{ mut .baz(b: mut B):read B-> { .bar->b}; }
"""));}
@Test void immLiteralTwoSupersLeaveSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:{ mut .m: A }
User:{ #: A -> C:A,B{} }
"""));}
@Test void readLiteralTwoSupersLeaveSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:{ mut .m: A }
User:{ #: read A -> read C:A,B{} }
"""));}
@Test void readLiteralDiamondLeavesSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:A{}
D:A{}
User:{ #: read A -> read C:B,D{} }
"""));}
@Test void readLiteralImplementsReadOverloadOfMergedMutAbstract(){ok(List.of("""
Z:{}
A:{ mut .m: Z; read .m: Z }
B:{ mut .m: Z; read .m: Z }
User:{ #: read A -> read C:A,B{ .m -> Z } }
"""));}
@Test void methodReceiverNotRcc(){fail("""
003|   .bar[X:imm,mut,read](x:X):A->x.foo123;
   |   -----------------------------^~~~~~~~

While inspecting method ".bar(_)" (line 3)
This call to method ".foo123" cannot typecheck.
The receiver has type "X", where "X" is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

Relevant code with inferred types:
A:{.foo123:A->this.foo123;.bar[X:*](x:X):A->x.foo123}
""", List.of("""
A:{
  .foo123:A->this.foo123;
  .bar[X:imm,mut,read](x:X):A->x.foo123;
}
"""));}

@Test void methodTArgsArityError(){fail("""
003|   .bar:A->this.id[A,A](this);
   |   --------~~~~^^^~~~~~~~~~~~

While inspecting method ".bar" (line 3)
This call to method "A.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
Method ".id(_)" declares 1 generic type parameter.
Declared generic type parameters: "X".
This call provides 2 generic type arguments.

Relevant code with inferred types:
this.id[imm,A,A](this)
""", List.of("""
A:{
  .id[X:imm,mut,read](x:X):X->x;
  .bar:A->this.id[A,A](this);
}
"""));}

@Test void methodArgsDisagree(){fail("""
003|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^~~~~~

While inspecting method ".caller(_,_)" (line 3)
This call to method "A.f(_,_)" cannot typecheck.
Arguments 1 and 2 need different promotions, but a call uses one promotion for all its arguments.
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
  Argument 1 fails with: Allow mutH argument 2.
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.
  Argument 2 fails with: Allow readH arguments, Allow mutH argument 1.
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Relevant code with inferred types:
this.f(x,y)
""", List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void methodArgsDisagree2(){fail("""
004|   .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
   |   --------------------------------~~~~^^~~~~~~~~~~~~~~~~

While inspecting method ".caller(_,_)" (line 4)
This call to method "A.f(_,_)" cannot typecheck.
Arguments 1 and 2 need different promotions, but a call uses one promotion for all its arguments.
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
  Argument 1 fails with: Allow mutH argument 2.
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.
  Argument 2 fails with: Allow readH arguments, Allow mutH argument 1.
  Method call "ID#(_)" has type "mutH A" instead of a subtype of "iso A".

Relevant code with inferred types:
this.f(x,ID#[imm,mutH A](y))
""", List.of("""
ID:{#[T:**](x:T):T->x}
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
}
"""));}

@Test void noVar1Ok(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->Skip#(aaaa);
}
"""));}
@Test void noVar1Fail(){fail("""
004|   .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
   |   ---------------------------~~~~~~~~~~~~~~^^^^~--

While inspecting parameter "aaaa" > method ".foo" (line 4) > method ".f(_)" (line 4)
Parameter "aaaa" has type "mut A".
Parameter "aaaa" can observe mutation; thus it cannot be captured in the "imm" object literal "BB" (line 4).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
}
"""));}

@Test void noVar1FailAnon(){fail("""
004|   .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
   |   ------------------------~~~~~~~~~~~~~~^^^^~--

While inspecting parameter "aaaa" > method ".foo" (line 4) > method ".f(_)" (line 4)
Parameter "aaaa" has type "mut A".
Parameter "aaaa" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "B" (line 4).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
}
"""));}

@Test void noVarPassesWithRCFilters(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
}
"""));}

@Test void fullyAnnotetedDeepCall(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,read A](Id#[imm,read A](aaaa));}}
"""));}
@Test void deepCall(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
"""));}

@Test void hopelessArg_calls_pArgHasType(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~~~^^^^^^^^^^^^^~

While inspecting method ".foo" (line 6) > method ".f(_)" (line 6)
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
Method call "AsRead#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A" (As declared)
- "iso A" (Strengthen result)

Relevant code with inferred types:
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa))}}
""", List.of("""

B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}

@Test void bestLitName_anonLiteralNoImpl_withMeth(){ok(List.of("""
A:{}
Main:{
  .m:A -> {.foo:A->A }.foo
}
"""));}


@Test void err_bestLitName_anonLiteralNoImpl_missingMethod(){fail("""
003|   .m:A -> { .bar:A->A }.foo
   |   --------~~~~~~~~~~~~~^^^^

While inspecting method ".m" (line 3)
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on object literal instance of "A".

Available methods on object literal instance of "A":
- .bar:A

Relevant code with inferred types:
A{.bar:A->A}.foo
""", List.of("""
A:{}
Main:{
  .m:A -> { .bar:A->A }.foo
  }
"""));}

@Test void err_bestLitName_anonLiteralNoImpl_empty(){fail("""
004|    .m:A -> { }.foo
   |    --------~~~^^^^

While inspecting method ".m" (line 4)
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on type "A".
Type "A" does not have any methods.

Relevant code with inferred types:
A.foo
""", List.of("""

A:{}
 Main:{
   .m:A -> { }.foo
  }
"""));}
@Test void err_bestLitName_NamedLiteralNoImpl_empty(){fail("""
003|    .m:A -> B:{ }.foo
   |    --------~~~~~^^^^

While inspecting method ".m" (line 3)
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on object literal instance of "B".
Type "B" does not have any methods.

Relevant code with inferred types:
B:{}.foo
""", List.of("""
A:{}
 Main:{
   .m:A -> B:{ }.foo
  }
"""));}
@Test void anonReceiverSealedHeadSelfCall(){ok(List.of("""
Outer:{ .m: base.Void -> {'self .a: base.Void -> base.Void{}; .b: base.Void -> self.a }.b }
"""));}
@Test void anonReceiverSealedHead(){ok(List.of("""
Outer:{ .m: base.Void -> { .a: base.Void -> base.Void{} }.a }
"""));}
@Test void err_anonReceiverSealedHeadReturnsSelf(){fail("""
001| Outer:{ .m: base.Void -> {'self .a: Outer -> self}.a }
   |         ------------------------~~~~~~~~~~~~~^^^^---

While inspecting parameter "self" > method ".a" (line 1) > method ".m" (line 1)
Method ".a" inside the object literal "{...}" (line 1)
is implemented with an expression returning the anonymous type of the object literal at line 1, column 26.
Parameter "self" has type the anonymous type of the object literal at line 1, column 26 instead of a subtype of "Outer".

Relevant code with inferred types:
Outer:{.m:base.Void->{'self .a:Outer->self}.a}
""", List.of("""
Outer:{ .m: base.Void -> {'self .a: Outer -> self}.a }
"""));}
@Test void err_anonReceiverSealedHeadUnwrittenSig(){failWf("""
001| Outer:{ .m: base.Void -> { .a -> base.Void{} }.a }
   |                          --^^^^^^^^^^^^^^^^^--

While inspecting object literal "{...}"
Missing return type for method ".a".
Add an explicit return type before "->".
A method can omit types in its signature only when a supertype has a method ".a" to inherit the missing types from.
No supertype of object literal "{...}" has a method ".a".
""", List.of("""
Outer:{ .m: base.Void -> { .a -> base.Void{} }.a }
"""));}
@Test void anonReceiverSealedHeadCapturesGeneric(){ok(List.of("""
Outer:{ .m[X](x:X): base.Void -> { .a: X -> x; .b[Y](y:Y): Y -> y }.b(base.Void) }
"""));}
@Test void anonReceiverImplementableHeadGivesSignatures(){ok(List.of("""
A:{ .get(x:A): A }
Main:{ .m(a:A): A -> { .get(x) -> x }.get(a) }
"""));}
@Test void anonReceiverSealedHeadSamePkgGivesSignatures(){ok(List.of("""
S:base.Sealed{ .get(x:S): S }
Main:{ .m(s:S): S -> { .get(x) -> x }.get(s) }
"""));}

@Test void passInt(){ok(List.of("""
 Main:{ .m:base.Int -> +42 }
"""));}
@Test void passFloat(){ok(List.of("""
 Main:{ .m:base.Float -> +42.0 }
"""));}
@Test void passNat(){ok(List.of("""
 Main:{ .m:base.Nat -> 42 }
"""));}
@Test void passSStr(){ok(List.of("""
 Main:{ .m:base.Str -> `Hi` }
"""));}
@Test void passDStr(){ok(List.of("""
 Main:{ .m:base.Str -> "Hi" }
"""));}
@Test void failFloatForInt_compressedKeepsFloat(){fail("""
001|  Main:{ .m:base.Int -> +1.5 }
   |         ---------------^^^^

While inspecting object literal instance of "base.Float" > method ".m" (line 1)
The body of method ".m" of type declaration "Main" is an expression returning "base.Float".
Object literal is of type "base.Float" instead of a subtype of "base.Int".

Relevant code with inferred types:
Main:{.m:base.Int->+1.5}
""", List.of("""
 Main:{ .m:base.Int -> +1.5 }
"""));}
@Test void failIntTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Int -> +421381834238972893748972389723 }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Integer literal is out of range for "base.Int".
"base.Int" must be representable as a 64-bit signed integer.
Valid range: -9223372036854775808 .. 9223372036854775807.
This literal is: "421381834238972893748972389723".
If you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Int -> +421381834238972893748972389723 }
"""));}
@Test void failNatTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Nat -> 421381834238972893748972389723 }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Natural literal is out of range for "base.Nat".
"base.Nat" must be representable as a 64-bit unsigned integer.
Valid range: 0 .. 18446744073709551615.
This literal is: "421381834238972893748972389723".
If you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Nat -> 421381834238972893748972389723 }
"""));}

@Test void failFloatTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e309 }
   |                          ^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e309".
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e309 }
"""));}
@Test void failFloatExponentBeyondIntRange(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e99999999999 }
   |                          ^^^^^^^^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e99999999999".
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e99999999999 }
"""));}
@Test void failFloatNegativeExponentBeyondIntRange(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e-99999999999 }
   |                          ^^^^^^^^^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e-99999999999".
If rounded, the nearest representable value is "+0.0".
Write "+1.0e-99999999999soft" to accept that rounding.
If you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e-99999999999 }
"""));}
@Test void okFloatZeroExponentBeyondIntRange(){ok(List.of("""
 Main:{ .m:base.Float -> +0.0e-99999999999 }
"""));}
@Test void failNumberLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: A -> 1[A] }
   |              ^^

While inspecting a literal
Literal "1" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "1".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: A -> 1[A] }
"""));}
@Test void failNumberLiteralWithEmptyTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: A -> 1[] }
   |              ^^

While inspecting a literal
Literal "1" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "1".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: A -> 1[] }
"""));}
@Test void failStrLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: `a`[A] }
   |         ^^^^

While inspecting a literal
Literal "`a`" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "`a`".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: `a`[A] }
"""));}
@Test void failUStrLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: "a"[A] }
   |         ^^^^

While inspecting a literal
Literal `"a"` is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after `"a"`.
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: "a"[A] }
"""));}
@Test void failFloatLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: A -> -1.5[] }
   |              ^^^^^

While inspecting a literal
Literal "-1.5" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "-1.5".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: A -> -1.5[] }
"""));}
@Test void failFloatTooSmall(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e-400 }
   |                          ^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e-400".
If rounded, the nearest representable value is "+0.0".
Write "+1.0e-400soft" to accept that rounding.
If you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e-400 }
"""));}
@Test void failFloatImprecise1(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +0.1 }
   |                          ^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+0.1".
If rounded, the nearest representable value is "+0.1000000000000000055511151231257827021181583404541015625".
Write "+0.1soft" to accept that rounding.
If you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +0.1 }
"""));}
@Test void failFloatImprecise2(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +0.2 }
   |                          ^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+0.2".
If rounded, the nearest representable value is "+0.200000000000000011102230246251565404236316680908203125".
Write "+0.2soft" to accept that rounding.
If you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +0.2 }
"""));}
@Test void everyZeroLiteralIsThePositiveZero(){
  assertEquals(List.of("0.0d", "0.0d", "0.0d", "0.0d", "0.0d"),
    List.of("-0.0", "+0.0", "0.0", "-0__0.000", "-0.0e5").stream().map(LiteralDeclarations::toJavaLiteral).toList());
}
@Test void floatExactFearlessLitScientific(){
  assertEquals("+9.31322574615478515625e-10", LiteralDeclarations.floatExactFearlessLit(Math.scalb(1.0, -30)));
  assertEquals("-9.31322574615478515625e-10", LiteralDeclarations.floatExactFearlessLit(-Math.scalb(1.0, -30)));
}
@Test void okFloatTooBig(){ok(List.of("""
 Main:{ .m:base.Float -> +179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0 }
"""));}
@Test void okFloatPrecise1(){ok(List.of("""
 Main:{ .m:base.Float ->  +0.1000000000000000055511151231257827021181583404541015625 }
"""));}
@Test void okFloatPrecise2(){ok(List.of("""
 Main:{ .m:base.Float -> +0.200000000000000011102230246251565404236316680908203125 }
"""));}
@Test void okFloatSoft(){ok(List.of("""
 Main:{ .m:base.Float -> +0.1soft }
"""));}
@Test void okFloatSoftUnsigned(){ok(List.of("""
 Main:{ .m:base.Float -> 0.4soft }
"""));}
@Test void okFloatSoftAlreadyExact(){ok(List.of("""
 Main:{ .m:base.Float -> +0.5soft }
"""));}
@Test void okFloatSoftUnderscores(){ok(List.of("""
 Main:{ .m:base.Float -> +1_0.4soft }
"""));}
@Test void failFloatSoftTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e309soft }
   |                          ^^^^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e309soft".
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e309soft }
"""));}

@Test void byNameOk1(){ok(List.of("""
 A:{.foo:A->A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameOk2(){ok(List.of("""
 A:{.foo:A->A}
 B:A{}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}
@Test void byNameFail1(){fail("""
003|  Main:{ .m:B -> B }
   |         --------^

While inspecting object literal instance of "B" > method ".m" (line 3)
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Add an implementation for ".foo" inside the object literal.
""", List.of("""
 A:{.foo:A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameFail2(){fail("""
003|  Main:{ .m:B -> B{.bar:A->A} }
   |         --------^^^^^^^^^^^^

While inspecting object literal instance of "B" > method ".m" (line 3)
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "B".
Add an implementation for ".foo" inside the object literal.

Relevant code with inferred types:
B{.bar:A->A}
""", List.of("""
 A:{.foo:A->A}
 B:A{.foo:A}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}

@Test void byNameOkMut(){ok(List.of("""
 A:{mut .foo:A->A}
 B:A{.foo:A}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}

@Test void captureFreeThisIsNotMut(){fail("""
002|  B:A,base.CaptureFree{ .get->this; }
   |                        ------^^^^

While inspecting parameter "this" > method ".get" (line 2)
The body of method ".get" of type declaration "B" is an expression returning "B".
Parameter "this" has type "B" instead of a subtype of "mut A".
Type declaration "B" implements "base.CaptureFree", so parameter "this" is "imm" in every method.
A value of "B" is never "mut", so "mut .get" can stay abstract.
A method written without a receiver capability also implements "mut .get": write the receiver capability, as in "read .get".

Relevant code with inferred types:
B:A,base.CaptureFree{read .get:read A->this;mut .get:mut A->this}
""", List.of("""
 A:{ read .get: read A; mut .get: mut A; }
 B:A,base.CaptureFree{ .get->this; }
"""));}
@Test void captureFreeThisReadOnly(){ok(List.of("""
 A:{ read .get: read A; mut .get: mut A; }
 B:A,base.CaptureFree{ read .get->this; }
 Main:{ .m:B -> B }
"""));}
@Test void byNameAbstractMutImm(){ok(List.of("""
 A:{mut .foo:A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameAbstractMutMut(){fail("""
003|  Main:{ .m:mut B -> mut B }
   |         ------------^^^^^

While inspecting object literal instance of "mut B" > method ".m" (line 3)
This object literal is missing a required method.
Missing: "mut .foo".
Required by: "A".
Add an implementation for ".foo" inside the object literal.
""", List.of("""
 A:{mut .foo:A}
 B:A{}
 Main:{ .m:mut B -> mut B }
"""));}

@Test void simpleBox(){ok(List.of("""
Box[EE:*]:{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  }
Boxs1:{#[ET:*](e:ET):mut Box[ET]->{
  mut .get ->e;
  read .get ->e;
  imm .get ->e;
  }}
Boxs:{#[ET:*](e:ET):mut Box[ET]->{e}}
"""));}

@Test void toStr(){ok(List.of("""
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }
Box[EE:*]: ToStr[EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .str by-> by#(this.get).str
  }
A:ToStr{ .str->Str}
Top:{
  .m00(b:Box[A]):Str -> b.str {::};
  .m01(b:Box[read A]):Str -> b.str {::};
  .m02(b:Box[mut A]):Str -> b.str {::};
  .m03(b:read Box[A]):Str -> b.str {::};
  .m04(b:read Box[read A]):Str -> b.str {::};
  .m05(b:read Box[mut A]):Str -> b.str {::};
  .m06(b:mut Box[A]):Str -> b.str {::};
  .m07(b:mut Box[read A]):Str -> b.str {::};
  .m08(b:mut Box[mut A]):Str -> b.str {::};
  .m09(b:iso Box[A]):Str -> b.str {::};
  .m10(b:iso Box[read A]):Str -> b.str {::};
  .m11(b:iso Box[mut A]):Str -> b.str {::};
  .m12(b:readH Box[A]):Str -> b.str {::};
  .m13(b:readH Box[read A]):Str -> b.str {::};
  .m14(b:readH Box[mut A]):Str -> b.str {::};
  .m15(b:mutH Box[A]):Str -> b.str {::};
  .m16(b:mutH Box[read A]):Str -> b.str {::};
  .m17(b:mutH Box[mut A]):Str -> b.str {::};
  }
"""));}
@Test void toStrToImm(){ok(List.of("""
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }
ToImm[T]:{ read .imm: T }
ToImmBy[T]:{#(read T):read ToImm[T]}
ToImm[T,E:*,TE]:{ read .imm(ToImmBy[imm E]): TE }
Box[EE:*]: ToStr[EE], ToImm[Box[EE],EE,Box[imm EE]]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .str by-> by#(this.get).str;
  .imm by-> Boxs#(by#(this.get).imm);
  }
Boxs1:{#[ET:*](e:ET):mut Box[ET]->{
  mut .get ->e;
  read .get ->e;
  imm .get ->e;
  }}
Boxs:{#[ET:*](e:ET):mut Box[ET]->{e}}

A:ToStr,ToImm[A]{ .str->Str; .imm->A}
TopToStr:{
  .m00(b:Box[A]):Str -> b.str {::};
  .m01(b:Box[read A]):Str -> b.str {::};
  .m02(b:Box[mut A]):Str -> b.str {::};
  .m03(b:read Box[A]):Str -> b.str {::};
  .m04(b:read Box[read A]):Str -> b.str {::};
  .m05(b:read Box[mut A]):Str -> b.str {::};
  .m06(b:mut Box[A]):Str -> b.str {::};
  .m07(b:mut Box[read A]):Str -> b.str {::};
  .m08(b:mut Box[mut A]):Str -> b.str {::};
  .m09(b:iso Box[A]):Str -> b.str {::};
  .m10(b:iso Box[read A]):Str -> b.str {::};
  .m11(b:iso Box[mut A]):Str -> b.str {::};
  .m12(b:readH Box[A]):Str -> b.str {::};
  .m13(b:readH Box[read A]):Str -> b.str {::};
  .m14(b:readH Box[mut A]):Str -> b.str {::};
  .m15(b:mutH Box[A]):Str -> b.str {::};
  .m16(b:mutH Box[read A]):Str -> b.str {::};
  .m17(b:mutH Box[mut A]):Str -> b.str {::};
  }
TopToImm:{
  .m00(b:Box[A]):Box[A] -> b.imm {::};
  .m01(b:Box[read A]):Box[A] -> b.imm {::};
  .m02(b:Box[mut A]):Box[A] -> b.imm {::};
  .m03(b:read Box[A]):Box[A] -> b.imm {::};
  .m04(b:read Box[read A]):Box[A] -> b.imm {::};
  .m05(b:read Box[mut A]):Box[A] -> b.imm {::};
  .m06(b:mut Box[A]):Box[A] -> b.imm {::};
  .m07(b:mut Box[read A]):Box[A] -> b.imm {::};
  .m08(b:mut Box[mut A]):Box[A] -> b.imm {::};
  .m09(b:iso Box[A]):Box[A] -> b.imm {::};
  .m10(b:iso Box[read A]):Box[A] -> b.imm {::};
  .m11(b:iso Box[mut A]):Box[A] -> b.imm {::};
  .m12(b:readH Box[A]):Box[A] -> b.imm {::};
  .m13(b:readH Box[read A]):Box[A] -> b.imm {::};
  .m14(b:readH Box[mut A]):Box[A] -> b.imm {::};
  .m15(b:mutH Box[A]):Box[A] -> b.imm {::};
  .m16(b:mutH Box[read A]):Box[A] -> b.imm {::};
  .m17(b:mutH Box[mut A]):Box[A] -> b.imm {::};
  }
"""));}
@Test void toOrder(){ok(List.of("""
use base.Bool as Bool; use base.True as True; use base.False as False; use base.Block as Block; use base.F as F;
Str:{}
OrderMatch[R:**]:{ mut .lt:R; mut .eq:R; mut .gt:R; }
Order[T]: {
  read .close:read T;
  read .cmp[R:**](a:read T,b:read T,m: mut OrderMatch[R]): R;
  read ==  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> False});
  read <=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->True; .gt -> False});
  read >=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> True});
  read <   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> False});
  read >   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->False; .gt -> True});
  read !=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> True});
  }
OrderBy[T]:{
  #(read T):read Order[T];
  .then(other:OrderBy[T]):OrderByCmp[T] -> {
    .cmp(a,b,m)-> this#a
      .cmp(a,b,{.lt ->m.lt; .eq ->other#a.cmp(a,b,m); .gt ->m.gt})
    };
  .view[AA](f:F[read AA,read Order[T]]):OrderByCmp[AA] -> {a,b,m-> f#a.cmp(f#a.close,f#b.close,m)};
}
OrderByCmp[T]:OrderBy[T]{
  .cmp[R:**](a:read T,b:read T,m:mut OrderMatch[R]): R;
  # a0 -> { .close -> a0; .cmp a,b,m -> this.cmp(a,b,m) };
  }
Order[T,E:*]:{
  read .close:read T;
  read .cmp[R:**](by: OrderBy[imm E], a:read T,b:read T, m: mut OrderMatch[R]): R;
  read .order(by: OrderBy[imm E]): read Order[T] -> {
    .close -> this.close;
    .cmp a,b,m -> this.cmp(by,a,b,m);
    };
  }
Box[EE:*]: Order[Box[EE],EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .close->this;
  .cmp by, a, b, m-> by#(a.get).cmp(a.get[read],b.get[read],m);
  }
A:Order[A]{ .close->this; .cmp a, b, m-> m.eq}
Top:{
  .m00(b:Box[A]):Bool -> b.order{::} == b;
  .m01(b:Box[read A]):Bool -> b.order{::} == b;
  .m02(b:Box[mut A]):Bool -> b.order{::} == b;
  .m03(b:read Box[A]):Bool -> b.order{::} == b;
  .m04(b:read Box[read A]):Bool -> b.order{::} == b;
  .m05(b:read Box[mut A]):Bool -> b.order{::} == b;
  .m06(b:mut Box[A]):Bool -> b.order{::} == b;
  .m07(b:mut Box[read A]):Bool -> b.order{::} == b;
  .m08(b:mut Box[mut A]):Bool -> b.order{::} == b;
  .m09(b1:iso Box[A],b2:iso Box[A]):Bool -> b1.order{::} == b2;
  .m10(b1:iso Box[read A],b2:iso Box[read A]):Bool -> b1.order{::} == b2;
  .m11(b1:iso Box[mut A],b2:iso Box[mut A]):Bool -> b1.order{::} == b2;
  .m12(b:readH Box[A]):Bool -> b.order{::} == b;
  .m13(b:readH Box[read A]):Bool -> b.order{::} == b;
  .m14(b:readH Box[mut A]):Bool -> b.order{::} == b;
  .m15(b:mutH Box[A]):Bool -> b.order{::} == b;
  .m16(b:mutH Box[read A]):Bool -> b.order{::} == b;
  .m17(b:mutH Box[mut A]):Bool -> b.order{::} == b;
  }
"""));}
static String flatMapDecs= """
use base.F as F;
List[E:*]:{}
Cat:{}
Person:{ .cats: List[Cat]; .mcats: mut List[Cat]; }
Flow[E:*]:{ mut .flatMap[R:*](f: read F[E, read List[R]]): mut Flow[read/imm R] }
""";
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameter(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap{::.cats} }
"""));}
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameterWithTargs(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap[Cat]{::.cats} }
"""));}
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameterMutBody(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap{::.mcats} }
"""));}
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameterExplicitHead(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap(read F[Person, read List[Cat]]{::.mcats}) }
"""));}
@Test void lambdaKeepsTheReadTypeVariableArgumentOfItsParameter(){ok(List.of(flatMapDecs+"""
Viewer[T]:{ .view[A](f: F[read A, read T]): Viewer[A] }
User:{ .m[T](v: Viewer[T], x: imm T): Viewer[Cat] -> v.view{c -> x} }
"""));}
@Test void lambdaKeepsTheReadTypeVariableArgumentOfItsParameterMutBody(){ok(List.of(flatMapDecs+"""
Viewer[T:*]:{ .view[A](f: F[read A, read T]): Viewer[A] }
User:{ .m[T:*](v: Viewer[T], x: F[mut T]): Viewer[Cat] -> v.view{c -> x#} }
"""));}
@Test void toOrderHash(){ok(List.of("""
use base.Nat as Nat; use base.Bool as Bool; use base.True as True; use base.False as False; use base.Block as Block; use base.F as F;
Str:{}
OrderMatch[R:**]:{ mut .lt:R; mut .eq:R; mut .gt:R; }
Order[T]: {
  read .close:read T;
  read .cmp[R:**](a:read T,b:read T,m: mut OrderMatch[R]): R;
  read ==  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> False});
  read <=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->True; .gt -> False});
  read >=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> True});
  read <   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> False});
  read >   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->False; .gt -> True});
  read !=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> True});
  }
OrderBy[T]:{
  #(read T):read Order[T];
  .then(other:OrderBy[T]):OrderByCmp[T] -> {
    .cmp a,b,m -> this#a
      .cmp(a,b,{.lt ->m.lt; .eq ->other#a.cmp(a,b,m); .gt ->m.gt})
    };
  .thenKey[TF](k:FF[T,TF]): OrderByCmp[T] -> this.then(By2#k);
  .view[A](f:F[read A,read T]):OrderByCmp[A] -> {a,b,m -> this#(f#a).cmp(f#a,f#b,m)};
}
OrderByCmp[T]:OrderBy[T]{
  .cmp[R:**](a:read T,b:read T,m:mut OrderMatch[R]): R;
  # a0 -> { .close -> a0; .cmp a,b,m -> this.cmp(a,b,m) };
  }
Order[T,E:*]:{
  read .close:read T;
  read .cmp[R:**](by: OrderBy[imm E], a:read T,b:read T, m: mut OrderMatch[R]): R;
  read .order(by: OrderBy[imm E]): read Order[T] -> {
    .close -> this.close;
    .cmp a,b,m -> this.cmp(by,a,b,m);
    };
  }
Hasher: {
  mut #[A,B](a: read OrderHash[A], b: read OrderHash[B]): Nat -> a.hash(this) * 31 + (b.hash(this));
  }
OrderHash[T]:Order[T]{ read .hash(h: mut Hasher): Nat }
OrderHash[T,E:*]:Order[T,E]{
  read .hash(by: OrderHashBy[imm E], h: mut Hasher): Nat;
  read .orderHash(by: OrderHashBy[imm E]): read OrderHash[T] -> {
    .close -> this.close;
    .cmp a,b,m -> this.cmp(by,a,b,m);
    .hash h -> this.hash(by,h);
    };
  }
OrderHashBy[T]:OrderBy[T]{
  #(x:read T): read OrderHash[T];
  .thenHash(other: OrderHashBy[T]): OrderHashByCmp[T] -> {
    .cmp a,b,m -> this#a
      .cmp(a,b,{.lt ->m.lt; .eq ->other#a.cmp(a,b,m); .gt ->m.gt});
    .hash a,h -> h#(this#a, other#a);
    };
  .viewHash[A](f:F[read A,read T]):OrderHashByCmp[A] -> {
    .cmp a,b,m -> this#(f#a).cmp(f#a,f#b,m);
    .hash a,h -> this#(f#a).hash(h);
    };
  }
OrderHashByCmp[T]:OrderHashBy[T]{
  .cmp[R:**](a:read T,b:read T,m:mut OrderMatch[R]): R;
  .hash(a: read T,h: mut Hasher):Nat;
  # a0 -> {
    .close -> a0;
    .cmp a,b,m -> this.cmp(a,b,m);
    .hash h -> this.hash(a0,h);
    };
  }
Box[EE:*]: OrderHash[Box[EE],EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .close->this;
  .cmp by, a, b, m-> by#(a.get).cmp(a.get[read],b.get[read],m);
  .hash by, h -> by#(this.get).hash h;
  }
A1:OrderHash[A1]{
  .close -> this;
  .cmp a, b, m -> m.eq;
  .hash h -> 0;
  }
Top:{
  .m00(b:Box[A1]):Bool -> b.order{::} == b;
  .m01(b:Box[read A1]):Bool -> b.order{::} == b;
  .m02(b:Box[mut A1]):Bool -> b.order{::} == b;
  .m03(b:read Box[A1]):Bool -> b.order{::} == b;
  .m04(b:read Box[read A1]):Bool -> b.order{::} == b;
  .m05(b:read Box[mut A1]):Bool -> b.order{::} == b;
  .m06(b:mut Box[A1]):Bool -> b.order{::} == b;
  .m07(b:mut Box[read A1]):Bool -> b.order{::} == b;
  .m08(b:mut Box[mut A1]):Bool -> b.order{::} == b;
  .m09(b1:iso Box[A1],b2:iso Box[A1]):Bool -> b1.order{::} == b2;
  .m10(b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> b1.order{::} == b2;
  .m11(b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> b1.order{::} == b2;
  .m12(b:readH Box[A1]):Bool -> b.order{::} == b;
  .m13(b:readH Box[read A1]):Bool -> b.order{::} == b;
  .m14(b:readH Box[mut A1]):Bool -> b.order{::} == b;
  .m15(b:mutH Box[A1]):Bool -> b.order{::} == b;
  .m16(b:mutH Box[read A1]):Bool -> b.order{::} == b;
  .m17(b:mutH Box[mut A1]):Bool -> b.order{::} == b;
  }
ThenHashBoxAll:{
  .thA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  }
ThenHashLeBoxAll:{
  .leA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],y:read Box[A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],y:read Box[read A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],y:read Box[mut A1]):Bool ->
    o.thenHash(p)#x <= y;
  }
ThenLeSelf:{
  .leA(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1]):Bool -> o.then(p)#x <= x;
  .leR(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1]):Bool -> o.then(p)#x <= x;
  .leM(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1]):Bool -> o.then(p)#x <= x;
}
ViewBoxAll18:{
  .v00(by:OrderBy[A1],b:Box[A1],c:Box[A1]):Bool -> by.view({x->x.get})#b <= c;
  .v01(by:OrderBy[A1],b:read Box[A1],c:read Box[A1]):Bool -> by.view{x->x.get}#b <= c;
  .v02(by:OrderBy[A1],b:mut Box[A1],c:mut Box[A1]):Bool -> by.view{::.get}#b <= c;
  .v03(by:OrderBy[A1],b1:iso Box[A1],b2:iso Box[A1]):Bool -> by.view({x->x.get})#b1 == b2;
  .v04(by:OrderBy[A1],b:readH Box[A1],c:readH Box[A1]):Bool -> by.view({x->x.get})#b != c;
  .v05(by:OrderBy[A1],b:mutH Box[A1],c:mutH Box[A1]):Bool -> by.view({x->x.get})#b >= c;

  .v06(by:OrderBy[A1],b:Box[read A1],c:Box[read A1]):Bool -> by.view({x->x.get})#b > c;
  .v07(by:OrderBy[A1],b:read Box[read A1],c:read Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v08(by:OrderBy[A1],b:mut Box[read A1],c:mut Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v09(by:OrderBy[A1],b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v10(by:OrderBy[A1],b:readH Box[read A1],c:readH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v11(by:OrderBy[A1],b:mutH Box[read A1],c:mutH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;

  .v12(by:OrderBy[A1],b:Box[mut A1],c:Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v13(by:OrderBy[A1],b:read Box[mut A1],c:read Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v14(by:OrderBy[A1],b:mut Box[mut A1],c:mut Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v15(by:OrderBy[A1],b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v16(by:OrderBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v17(by:OrderBy[A1],b:mutH Box[mut A1],c:mutH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;

  .vh0(by:OrderHashBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.viewHash({x->x.get})#b <= c;
  .vh1(by:OrderHashBy[A1],b:mutH Box[mut A1],h:iso Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
  .vh2(by:OrderHashBy[A1],b:mut Box[mut A1],h:mut Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
}
By:{ #[T](by: OrderBy[T]): OrderBy[T] -> by; }
ByHash:{ #[T](by: OrderHashBy[T]): OrderHashBy[T] -> by; }

Age:OrderHash[Age]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Name:OrderHash[Name]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Person:{ read .age: Age; read .name: Name; }

AndThenTests:{
  read .orderOk0: OrderBy[Person] ->
    By#[Age]{::}.view[Person]{::.age};
  read .orderOk1: OrderBy[Person] ->
    By#[Age]{::}.view{::.age};
  read .orderOk: OrderBy[Person] ->
    By#[Age]{::}.view{::.age}
    .then(By#[Name]{::}.view({p->p.name}));
  read .hashOk: OrderHashBy[Person] ->
    ByHash#[Age]{::}.viewHash{::.age}
    .thenHash(ByHash#[Name]{::}.viewHash{::.name});
}
FF[A,T]:{#(read A): read Order[T]}
By2:{
  #[T,A](f:FF[A,T]): OrderByCmp[A] -> {
    .cmp a,b,m -> (f#a).cmp((f#a).close,(f#b).close,m);
  };
}
AndThenTests2:{
  read .orderOk0: OrderBy[Person] ->
    By2#{::.age};
  read .orderOk: OrderBy[Person] ->
    By2#{::.age}.thenKey{::.name};
  }
"""));}
@Test void toOrderHashDesign3(){ok(List.of("""
use base.Nat as Nat; use base.Bool as Bool; use base.True as True; use base.False as False; use base.Block as Block; use base.F as F;
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }

OrderMatch[R:**]:{ mut .lt:R; mut .eq:R; mut .gt:R; }

Order[T]: {
  read .close: read T;
  read .cmp[R:**](t0: read T, t1: read T, m: mut OrderMatch[R]): R;

  read ==  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> False});
  read <=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->True; .gt -> False});
  read >=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> True});
  read <   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> False});
  read >   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->False; .gt -> True});
  read !=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> True});

  read <=>[R:**](other: read Order[T], m: mut OrderMatch[R]): R -> this.cmp(this.close, other.close, m);
}
OrderBy[T,K]:{
  #(read T): read Order[K];
  .then[K0](next: OrderBy[T,K0]): OrderBy[T] -> {
    .cmp(t0,t1,m)-> this#t0 <=>
      (this#t1, {.lt->m.lt; .gt->m.gt; .eq->next#t0<=>(next#t1,m);})
  };
  .view[A](f:F[read A,read T]):OrderBy[A] ->
    {a0,a1,m-> this#(f#a0)<=>(this#(f#a1),m)};
}
OrderBy[T]:OrderBy[T,T]{
  .cmp[R:**](t0:read T,t1:read T,m:mut OrderMatch[R]): R;
  # t -> { .close -> t; .cmp t0,t1,m -> this.cmp(t0,t1,m) };
}
Order[T,E:*]:{
  read .close:read T;
  read .cmp[K,R:**](by: OrderBy[imm E,K], t0:read T,t1:read T, m: mut OrderMatch[R]): R;
  read .order[K](by: OrderBy[imm E,K]): read Order[T] -> {
    .close -> this.close;
    .cmp t0,t1,m -> this.cmp(by,t0,t1,m);
  };
}
Hasher: {
  mut #[A,B](a: read OrderHash[A], b: read OrderHash[B]): Nat -> a.hash(this) * 31 + (b.hash(this));
}
OrderHash[T]:Order[T],ToStr{ read .hash(h: mut Hasher): Nat }
OrderHash[T,E:*]:Order[T,E],ToStr[E]{
  read .hash[K](by: OrderHashBy[imm E,K], h: mut Hasher): Nat;
  read .orderHash[K](by: OrderHashBy[imm E,K]): read OrderHash[T] -> {
    .close -> this.close;
    .cmp t0,t1,m -> this.cmp(by,t0,t1,m);
    .hash h -> this.hash(by,h);
    .str  -> this.str by;
  };
}
OrderHashBy[T,K]:OrderBy[T,K],ToStrBy[T]{
  #(t:read T): read OrderHash[K];
  .thenHash[K0](next: OrderHashBy[T,K0]): OrderHashBy[T] -> {
    .cmp t0,t1,m -> this#t0<=>(this#t1,{
      .lt ->m.lt;
      .eq ->next#t0<=>(next#t1,m);
      .gt ->m.gt});
    .hash t,h -> h#(this#t, next#t);
  };
  .viewHash[A](f:F[read A,read T]):OrderHashBy[A] -> {
    .cmp a0,a1,m -> this#(f#a0)<=>(this#(f#a1),m);
    .hash a,h -> this#(f#a).hash(h);
  };
}
OrderHashBy[T]:OrderHashBy[T,T]{
  .cmp[R:**](t0:read T,t1:read T,m:mut OrderMatch[R]): R;
  .hash(t: read T,h: mut Hasher):Nat;
  # t -> {
    .close -> t;
    .cmp t0,t1,m -> this.cmp(t0,t1,m);
    .hash h -> this.hash(t,h);
    .str -> this#t.str;
  };
}
Box[E:*]: OrderHash[Box[E],E]{
  mut  .get: E;
  read .get: read/imm E;
  imm  .get: imm E;
  .close->this;
  .cmp by, t0, t1, m-> by#(t0.get)<=>(by#(t1.get),m);
  .hash by, h -> by#(this.get).hash h;
  .str by->by#(this.get).str;
  .proofConcrete(s:Str):Box[Str]->Box[Str]{ .get->s; };//this also tests good handling of RC overloading
}
A1:OrderHash[A1]{
  .close -> this;
  .cmp t0, t1, m -> m.eq;
  .hash h -> 0;
  .str ->Str;
  .proofConcrete:A1->A1;
}
Top:{
  .m00(b:Box[A1]):Bool -> b.order{::} == b;
  .m01(b:Box[read A1]):Bool -> b.order{::} == b;
  .m02(b:Box[mut A1]):Bool -> b.order{::} == b;
  .m03(b:read Box[A1]):Bool -> b.order{::} == b;
  .m04(b:read Box[read A1]):Bool -> b.order{::} == b;
  .m05(b:read Box[mut A1]):Bool -> b.order{::} == b;
  .m06(b:mut Box[A1]):Bool -> b.order{::} == b;
  .m07(b:mut Box[read A1]):Bool -> b.order{::} == b;
  .m08(b:mut Box[mut A1]):Bool -> b.order{::} == b;
  .m09(b1:iso Box[A1],b2:iso Box[A1]):Bool -> b1.order{::} == b2;
  .m10(b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> b1.order{::} == b2;
  .m11(b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> b1.order{::} == b2;
  .m12(b:readH Box[A1]):Bool -> b.order{::} == b;
  .m13(b:readH Box[read A1]):Bool -> b.order{::} == b;
  .m14(b:readH Box[mut A1]):Bool -> b.order{::} == b;
  .m15(b:mutH Box[A1]):Bool -> b.order{::} == b;
  .m16(b:mutH Box[read A1]):Bool -> b.order{::} == b;
  .m17(b:mutH Box[mut A1]):Bool -> b.order{::} == b;
  }
ThenHashBoxAll:{
  .thA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  }
ThenHashLeBoxAll:{
  .leA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],y:read Box[A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],y:read Box[read A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],y:read Box[mut A1]):Bool ->
    o.thenHash(p)#x <= y;
  }
ThenLeSelf:{
  .leA(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1]):Bool -> o.then(p)#x <= x;
  .leR(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1]):Bool -> o.then(p)#x <= x;
  .leM(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1]):Bool -> o.then(p)#x <= x;
}
ViewBoxAll18:{
  .v00(by:OrderBy[A1],b:Box[A1],c:Box[A1]):Bool -> by.view({x->x.get})#b <= c;
  .v01(by:OrderBy[A1],b:read Box[A1],c:read Box[A1]):Bool -> by.view{x->x.get}#b <= c;
  .v02(by:OrderBy[A1],b:mut Box[A1],c:mut Box[A1]):Bool -> by.view{::.get}#b <= c;
  .v03(by:OrderBy[A1],b1:iso Box[A1],b2:iso Box[A1]):Bool -> by.view({x->x.get})#b1 == b2;
  .v04(by:OrderBy[A1],b:readH Box[A1],c:readH Box[A1]):Bool -> by.view({x->x.get})#b != c;
  .v05(by:OrderBy[A1],b:mutH Box[A1],c:mutH Box[A1]):Bool -> by.view({x->x.get})#b >= c;

  .v06(by:OrderBy[A1],b:Box[read A1],c:Box[read A1]):Bool -> by.view({x->x.get})#b > c;
  .v07(by:OrderBy[A1],b:read Box[read A1],c:read Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v08(by:OrderBy[A1],b:mut Box[read A1],c:mut Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v09(by:OrderBy[A1],b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v10(by:OrderBy[A1],b:readH Box[read A1],c:readH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v11(by:OrderBy[A1],b:mutH Box[read A1],c:mutH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;

  .v12(by:OrderBy[A1],b:Box[mut A1],c:Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v13(by:OrderBy[A1],b:read Box[mut A1],c:read Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v14(by:OrderBy[A1],b:mut Box[mut A1],c:mut Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v15(by:OrderBy[A1],b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v16(by:OrderBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v17(by:OrderBy[A1],b:mutH Box[mut A1],c:mutH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;

  .vh0(by:OrderHashBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.viewHash({x->x.get})#b <= c;
  .vh1(by:OrderHashBy[A1],b:mutH Box[mut A1],h:iso Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
  .vh2(by:OrderHashBy[A1],b:mut Box[mut A1],h:mut Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
}
Age:OrderHash[Age]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Name:OrderHash[Name]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Person:{ read .age: Age; read .name: Name; }

CompareBy:{
  #[T,K](by:OrderBy[T,K]): OrderBy[T,K] -> by;
}
CompareBy2a[T]:{
  #[K](by:OrderBy[T,K]): OrderBy[T,K] -> by;
}
CompareBy2b[K]:{
  #[T](by:OrderBy[T,K]): OrderBy[T,K] -> by;
}
AndThenTests2:{
  .orderOk0: OrderBy[Person,Age] ->
    {::.age};
  .orderOk1: OrderBy[Person] ->
    CompareBy#{::.age}.then{::.name};
  .max[T](order:OrderBy[Person,T]):Person;
  .orderOk2:Person->this.max(CompareBy#{::.age}.then{::.name});
  .orderOk2a:Person->this.max(CompareBy2a[Person]#{::.age}.then{::.name});
  .orderOk2b:Person->this.max(CompareBy2b[Age]#{::.age}.then{::.name});
  .orderOk3:Person->this.max({::.age}.then{::.name});
  .orderOk4:Person->this.max({::.age});
}
"""));}

@Test void regressionOrderBy(){ok(List.of("""
Str:{}
Age:{}
Person:{ .age: Age; }
G2[A,T]:{
  .g2(A): T;
  .fooStr(s:Str):Str->s; // ok
  .fooA(a:A):A->a; //this used to break inference
  .fooT(t:T):T->t;   //this used to break inference
  .foo2(t:A):A->t;   //this used to break inference
  .fooT(t:T,tt:T):T->t;   //this used to break inference
}
G1[T]:G2[T,T]{ .foo2(t:T):T->t; }//this was always fine
Make:{ .make[A,K](f:G2[A,K]): G1[A] -> Make.make f; }
Tests:{ .ok: G1[Person] -> Make.make{
  .g2(p:Person):Age->p.age;
  }}
"""));}

@Test void regressionBangMatchWorksWithDiffNames(){ok(List.of("""
Str:{}
Boom:{ .msg[R:**](s: Str): R -> Boom.msg(s); }
BoxMatch[E:*,R:**]:{ mut .some(x: E): R; mut .empty: R; }
_Box[E:*]:{
  mut  .match[R:**](m: mut BoxMatch[E, R]): R;
  read .match[R:* ](m: mut BoxMatch[read/imm E, R]): R;
  imm  .match[R:* ](m: mut BoxMatch[imm E, R]): R;

  mut  !: E;
  read !!: read/imm E;
  imm  !!!: imm E;
}
Box[E:*]: _Box[E]{
  .match(m) -> this.match(m);
  ! -> this.match{ .some x -> x; .empty  -> Boom.msg Str; };
  !! -> this.match{ .some x -> x; .empty  -> Boom.msg Str; };
  !!! -> this.match{ .some x -> x; .empty  -> Boom.msg Str; };

}
"""));}

@Test void regressionBangMatch(){ok(List.of("""
Str:{}
Boom:{ .msg[R:**](s: Str): R -> Boom.msg(s); }
BoxMatch[E:*,R:**]:{ mut .some(x: E): R; mut .empty: R; }
_Box[E:*]:{
  mut  .match[R:**](m: mut BoxMatch[E, R]): R;
  read .match[R:* ](m: mut BoxMatch[read/imm E, R]): R;
  imm  .match[R:* ](m: mut BoxMatch[imm E, R]): R;

  mut  !: E;  //with only one of the 3 uncommented it works,
  read !: read/imm E;//with any 2 of them uncommented it fails
  imm  !: imm E;
}
Box[E:*]: _Box[E]{
  .match(m) -> this.match(m);
  ! -> this.match{ .some x -> x; .empty  -> base.Todo!; };
}
"""));}

@Test void slotReadOptAdaptsOnlyTheOpt(){fail("""
003| Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
004|   mut  .opt: mut Opt[E] -> e.get;
005|   read .opt: read Opt[read/imm E] -> e.get;
   |   -----------------------------------^^^^^
006|   } }

While inspecting method call ".get" > method ".opt" (line 5) > method "#(_)" (line 3)
Method ".opt" inside the object literal "mut Slot[_]" (line 3)
is implemented with an expression returning "read Opt[E]".
Method call "read Var[_].get" has type "read Opt[E]" instead of a subtype of "read Opt[read/imm E]".

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
Slots:{#[E:*](e:mut Var[mut Opt[E]]):mut Slot[E]->mut Slot[E:*]:{mut .opt->e.get[mut];read .opt:read Opt[read/imm E]->e.get[read]}}
""", List.of("""
Opt[E:*]:{}
Var[E:imm,mut,read]:{ read .get: read/imm E; mut .get: E; }
Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
  mut  .opt: mut Opt[E] -> e.get;
  read .opt: read Opt[read/imm E] -> e.get;
  } }
"""));}
@Test void slotReadOpt(){ok(List.of("""
Opt[E:*]:{}
Var[E:imm,mut,read]:{ read .get: read/imm E; mut .get: E; }
Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
  mut  .opt: mut Opt[E] -> e.get;
  read .opt: read Opt[E] -> e.get;
  } }
"""));}
@Test void slotReadOptFresh(){ok(List.of("""
Opt[E:*]:{ read .mapSome[R:*](f: mut F[read/imm E, R]): mut Opt[R]; }
F[A:*,R:*]:{ mut #(a: A): R; }
Var[E:imm,mut,read]:{ read .get: read/imm E; mut .get: E; }
Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
  mut  .opt: mut Opt[E] -> e.get;
  read .opt: mut Opt[read/imm E] -> e.get.mapSome{x -> x};
  } }
"""));}
@Test void readOptOfMutNotReadOptOfRead(){fail("""
003| User:{ .u(o: read Opt[mut X]): read Opt[read X] -> o; }
   |        --------------------------------------------^

While inspecting parameter "o" > method ".u(_)" (line 3)
The body of method ".u(_)" of type declaration "User" is an expression returning "read Opt[mut X]".
Parameter "o" has type "read Opt[mut X]" instead of a subtype of "read Opt[read X]".

Relevant code with inferred types:
User:{.u(o:read Opt[mut X]):read Opt[read X]->o}
""", List.of("""
Opt[E:*]:{}
X:{}
User:{ .u(o: read Opt[mut X]): read Opt[read X] -> o; }
"""));}


//----Testing name suggester
@Test void nameSuggester_1(){failExt("""
[###]
Did you mean "FooBar" ?
[###]
""", List.of("""
FooBar:{}
User:{.foo:Foo;}
"""));}

@Test void nameSuggester_2(){failExt("""
[###]
Did you mean "abcDef" ?
[###]
""", List.of("""
A:{}
User:{.foo(abc:A, abcDef:A):A->abcDeee;}
"""));}

@Test void nameSuggester_3(){failExt("""
[###]
Did you mean ".foo2" ?
[###]
""", List.of("""
A:{}
User:{
  .foo1:A->this.foo22;
  .foo2:A;
  .foo3:A;
  }
"""));}

// Missing TypeName

@Test void nameSuggester_4(){failExt("""
[###]
Did you mean "FooBar" ?
[###]
""", List.of("""
FooBar:{}
User:{.foo:FooBaar;}
"""));}

@Test void nameSuggester_5(){failExt("""
[###]
Did you mean "NumExact" ?
[###]
""", List.of("""
NumExact:{}
User:{.foo:Num;}
"""));}

@Test void nameSuggester_6(){failExt("""
[###]
Did you mean "ReadOnly" ?
[###]
""", List.of("""
ReadOnly:{}
User:{.foo:ReadOnyl;}
"""));}

@Test void nameSuggester_7(){failExt("""
[###]
Did you mean "HTTPServer" ?
[###]
""", List.of("""
HTTPServer:{}
User:{.foo:HttpServer;}
"""));}

@Test void nameSuggester_8(){failExt("""
[###]
Did you mean "JSONParser" ?
[###]
""", List.of("""
JSONParser:{}
User:{.foo:JsonParser;}
"""));}

@Test void nameSuggester_9(){failExt("""
[###]
Did you mean "XMLHttpRequest" ?
[###]
""", List.of("""
XMLHttpRequest:{}
User:{.foo:XmlHttpRequest;}
"""));}

@Test void nameSuggester_10(){failExt("""
[###]
Did you mean "URLDecoder" ?
[###]
""", List.of("""
URLDecoder:{}
User:{.foo:UrlDecoder;}
"""));}

@Test void nameSuggester_11(){failExt("""
[###]
Did you mean "ASCIIParser" ?
[###]
""", List.of("""
ASCIIParser:{}
User:{.foo:AsciiParser;}
"""));}

@Test void nameSuggester_12(){failExt("""
[###]
Did you mean "FooBar''''" ?
[###]
""", List.of("""
FooBar'''':{}
User:{.foo:FooBar'';}
"""));}

@Test void nameSuggester_13(){failExt("""
[###]
Did you mean "FooBar" ?
[###]
""", List.of("""
FooBar:{}
User:{.foo:Bar;}
"""));}

// Missing .methName

@Test void nameSuggester_14(){failExt("""
[###]
Did you mean ".numExact" ?
[###]
""", List.of("""
A:{}
User:{
  .numExact:A;
  .go:A->this.num;
  }
"""));}

@Test void nameSuggester_15(){failExt("""
[###]
Did you mean ".toJSON" ?
[###]
""", List.of("""
A:{}
User:{
  .toJSON:A;
  .go:A->this.toJson;
  }
"""));}

@Test void nameSuggester_16(){failExt("""
[###]
Did you mean ".parseXML" ?
[###]
""", List.of("""
A:{}
User:{
  .parseXML:A;
  .go:A->this.parseXml;
  }
"""));}

@Test void nameSuggester_17(){failExt("""
[###]
Did you mean ".myHttpServer" ?
[###]
""", List.of("""
A:{}
User:{
  .myHttpServer:A;
  .go:A->this.myHTTPServer;
  }
"""));}

@Test void nameSuggester_18(){failExt("""
[###]
Did you mean ".sha256" ?
[###]
""", List.of("""
A:{}
User:{
  .sha256:A;
  .go:A->this.sha265;
  }
"""));}

@Test void nameSuggester_19(){failExt("""
[###]
Did you mean ".foo'''''" ?
[###]
""", List.of("""
A:{}
User:{
  .foo''''':A;
  .go:A->this.foo'';
  }
"""));}

@Test void nameSuggester_20(){failExt("""
[###]
Did you mean ".readOnly" ?
[###]
""", List.of("""
A:{}
User:{
  .readOnly:A;
  .go:A->this.read;
  }
"""));}

@Test void nameSuggester_21(){failExt("""
[###]
Did you mean ".makeUUID" ?
[###]
""", List.of("""
A:{}
User:{
  .makeUUID:A;
  .go:A->this.makeUuid;
  }
"""));}

@Test void nameSuggester_22(){failExt("""
[###]
Did you mean ".asUTF8" ?
[###]
""", List.of("""
A:{}
User:{
  .asUTF8:A;
  .go:A->this.asUtf8;
  }
"""));}

@Test void nameSuggester_23(){failExt("""
[###]
Did you mean ".xmlHttpRequest" ?
[###]
""", List.of("""
A:{}
User:{
  .xmlHttpRequest:A;
  .go:A->this.xmlHTTPRequest;
  }
"""));}

// Missing parName

@Test void nameSuggester_24(){failExt("""
[###]
Did you mean "numExact" ?
[###]
""", List.of("""
A:{}
User:{.f(numExact:A):A->num;}
"""));}

@Test void nameSuggester_25(){failExt("""
[###]
Did you mean "toJSON" ?
[###]
""", List.of("""
A:{}
User:{.f(toJSON:A):A->toJson;}
"""));}

@Test void nameSuggester_26(){failExt("""
[###]
Did you mean "httpServer" ?
[###]
""", List.of("""
A:{}
User:{.f(httpServer:A):A->myHttpServer;}
"""));}

@Test void nameSuggester_27(){failExt("""
[###]
Did you mean "x'''''" ?
[###]
""", List.of("""
A:{}
User:{.f(x''''':A):A->x'';}
"""));}

@Test void nameSuggester_28(){failExt("""
[###]
Did you mean "byteBuffer" ?
[###]
""", List.of("""
A:{}
User:{.f(byteBuffer:A):A->buffer;}
"""));}

@Test void nameSuggester_29(){failExt("""
[###]
Did you mean "fooBarBaz" ?
[###]
""", List.of("""
A:{}
User:{.f(fooBarBaz:A):A->fooBarBax;}
"""));}

@Test void nameSuggester_30(){failExt("""
[###]
Did you mean "length" ?
[###]
""", List.of("""
A:{}
User:{.f(length:A):A->lenght;}
"""));}

@Test void nameSuggester_31(){failExt("""
[###]
Did you mean "sha256" ?
[###]
""", List.of("""
A:{}
User:{.f(sha256:A):A->sha265;}
"""));}

@Test void nameSuggester_32(){failExt("""
[###]
Did you mean "fooBar" ?
[###]
""", List.of("""
A:{}
User:{.f(fooBar:A):A->myFooBar;}
"""));}

@Test void nameSuggester_33(){failExt("""
[###]
Did you mean "httpServerPort" ?
[###]
""", List.of("""
A:{}
User:{.f(httpServerPort:A):A->serverPort;}
"""));}
@Test void genHeadReported(){fail("""
004| User:{.f(c:C[A]):C[B]->c;}
   |       -----------------^

While inspecting parameter "c" > method ".f(_)" (line 4)
The body of method ".f(_)" of type declaration "User" is an expression returning "C[A]".
Parameter "c" has type "C[A]" instead of a subtype of "C[B]".

Relevant code with inferred types:
User:{.f(c:C[A]):C[B]->c}
""", List.of("""
A:{}
B:{}
C[X]:{}
User:{.f(c:C[A]):C[B]->c;}
"""));}
@Test void genHeadReportedObjLit(){fail("""
004| User:{.f(c:C[A]):C[B]->C[A]{ .foo:A->A };}
   |       -----------------^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "C[A]" > method ".f(_)" (line 4)
The body of method ".f(_)" of type declaration "User" is an expression returning "C[A]".
Object literal is of type "C[A]" instead of a subtype of "C[B]".

Relevant code with inferred types:
User:{.f(c:C[A]):C[B]->C[A]{.foo:A->A}}
""", List.of("""
A:{}
B:{}
C[X]:{}
User:{.f(c:C[A]):C[B]->C[A]{ .foo:A->A };}
"""));}

@Test void badImplementsVoid(){ failExt("""
In file: [###].fear

006|   imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{ .foo(s:Sup):Sup->s } }
   |                                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.Void"
Object literal instance of "base.Void" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal instance of "base.Void" is in package "p".
Type "base.Void" is in package "base".
Error 7 WellFormedness
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{ .foo(s:Sup):Sup->s } }
}
"""));}

@Test void badImplicit(){ failExt("""
In file: [###].fear

003| User:Sup{ :: }
   |           ^^

While inspecting parameter "::" > method ".h(_)" (line 3)
The body of method ".h(_)" of type declaration "User" is an expression returning "Sup".
Parameter "::" has type "Sup" instead of a subtype of "base.Void".

Relevant code with inferred types:
User:Sup{.h(Sup):base.Void->::}
Error 8 TypeError
""", List.of("""

Sup:{ imm .h(x:Sup):base.Void; }
User:Sup{ :: }
"""));}

@Test void badSealed1(){ failExt("""
In file: [###].fear

001| ExtStr:"beer"{}
   | ^^^^^^^^^^^^^^^

While inspecting type declaration "ExtStr"
Type declaration "ExtStr" implements sealed type `"beer"`.
Sealed types can only be implemented in their own package.
Type declaration "ExtStr" is in package "p".
Type `"beer"` is in package "base".
Error 7 WellFormedness
""", List.of("""
ExtStr:"beer"{}
"""));}

@Test void tsWidenAnonLiteralHeadVsRequiredType(){fail("""
003| B:{.m:Target->Sup{}}
   |    -----------^^^^^

While inspecting object literal instance of "Sup" > method ".m" (line 3)
The body of method ".m" of type declaration "B" is an expression returning "Sup".
Object literal is of type "Sup" instead of a subtype of "Target".

Relevant code with inferred types:
B:{.m:Target->Sup}
""", List.of("""
Sup:base.WidenTo[Target]{}
Target:Sup{}
B:{.m:Target->Sup{}}
"""));}

@Test void tsWidenAnonLiteralHeadControlNoWiden(){fail("""
003| B:{.m:Target->Sup{}}
   |    -----------^^^^^

While inspecting object literal instance of "Sup" > method ".m" (line 3)
The body of method ".m" of type declaration "B" is an expression returning "Sup".
Object literal is of type "Sup" instead of a subtype of "Target".

Relevant code with inferred types:
B:{.m:Target->Sup}
""", List.of("""
Sup:{}
Target:Sup{}
B:{.m:Target->Sup{}}
"""));}

@Test void tsWidenAnonLiteralHeadMissingMethod(){fail("""
003| B:{.m:Target->Sup{.foo->base.Str}}
   |    -----------^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Sup" > method ".m" (line 3)
The body of method ".m" of type declaration "B" is an expression returning "Sup".
Object literal is of type "Sup" instead of a subtype of "Target".

Relevant code with inferred types:
B:{.m:Target->Sup{.foo:base.Str->base.Str}}
""", List.of("""
Sup:base.WidenTo[Target]{ .foo:base.Str }
Target:Sup{ .extra:base.Str }
B:{.m:Target->Sup{.foo->base.Str}}
"""));}

@Test void tsWidenNamedLiteralBody(){ok(List.of("""
Target:{ .foo(x:Target):Target }
Sup:{ .foo(x:base.Str):base.Str }
B:{ .m:Sup-> N:Sup,base.WidenTo[Target]{ .foo(x)->x } }
"""));}

@Test void tsWidenNamedLiteralBodyControlNoWiden(){ok(List.of("""
Target:{ .foo(x:Target):Target }
Sup:{ .foo(x:base.Str):base.Str }
B:{ .m:Sup-> N:Sup{ .foo(x)->x } }
"""));}

@Test void tsPromotionChanin(){ok(List.of("""
A:{ imm .a1: mut A; mut .a2: A;}
B:{ .b(a:A):A->a.a1.a2; }
C:{ .c(a:A):A->a.a1; }
D:{}
List[P:*]:{read .flow : mut Flow[P]; }
Flow[P:*]:{mut .map(read D): mut Flow[P]; mut .list:mut List[P]}
Names1:{ #(ps: List[A]): iso List[A] -> ps.flow.map iso D{}.list }
Names2:{ #(ps: List[A]): iso List[A] -> ps.flow.map {}.list }
"""));}

@Test void baseIdIdentity(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[Customer,Person] -> {::} }
"""));}
@Test void baseIdIdentityNamed(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->x }
"""));}
@Test void baseIdAsCall(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdAsCallExplicitTarg(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as[Person]{::} }
"""));}
@Test void baseIdNested(){ok(List.of("""
Person:{}
Customer:Person{}
User:{
  .m: base.BaseId[base.MList[Customer],base.MList[Person]] -> {::.as{::}};
  .n(css: base.MList[base.MList[Customer]]): base.MList[base.MList[Person]] -> css.as{::.as{::}};
  }
"""));}
@Test void baseIdAsImmListOfMutElements(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: base.MList[mut Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdAsNestedImmListsOfMutElements(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(css: base.MList[mut base.MList[mut Customer]]): base.MList[base.MList[Person]] -> css.as{::.as{::}} }
"""));}
@Test void baseIdAsMutList(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: mut base.MList[Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdAsReadListOfMutElements(){fail("""
003| User:{ .n(cs: read base.MList[mut Customer]): base.MList[Person] -> cs.as{::} }
   |        -------------------------------------------------------------------^^-

While inspecting parameter "::" > method "#(_)" (line 3) > method ".n(_)" (line 3)
Method "#(_)" inside the object literal instance of "base.BaseId[read Customer,Person]" (line 3)
is implemented with an expression returning "read Customer".
Parameter "::" has type "read Customer" instead of a subtype of "Person".

Relevant code with inferred types:
User:{.n(cs:read base.MList[mut Customer]):base.MList[Person]->cs.as[read,Person](base.BaseId[read Customer,Person]{#(read Customer):Person->::})}
""", List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: read base.MList[mut Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdProofKeepsTheTypeOfTheArgument(){ok(List.of("""
Person:{}
Customer:Person{ .n: base.Void }
Box[T]:{ .get: T }
Boxes:{ #[T](x: T, f: base.BaseId[T,Person]): Box[T] -> Boxes#(x,f) }
User:{ .m(c: Customer): base.Void -> Boxes#(c,{::}).get.n }
"""));}
@Test void inferenceKeepsTheTypeOfTheArgumentWithoutALiteral(){ok(List.of("""
Person:{}
Customer:Person{ .n: base.Void }
Box[T]:{ .get: T }
Boxes:{ #[T](x: T): Box[T] -> Boxes#x }
User:{ .m(c: Customer): base.Void -> Boxes#(c).get.n }
"""));}
@Test void inferenceKeepsTheTypeOfTheArgumentWithALambda(){ok(List.of("""
Person:{}
Customer:Person{ .n: base.Void }
Box[T]:{ .get: T }
Fn[A,B]:{ #(a: A): B }
Boxes:{ #[T](x: T, f: Fn[T,Person]): Box[T] -> Boxes#(x,f) }
User:{ .m(c: Customer): base.Void -> Boxes#(c,{x -> x}).get.n }
"""));}
@Test void baseIdNotSubtype(){fail("""
003| User:{ .m: base.BaseId[Person,Customer] -> {::} }
   |        -------------------------------------^^-

While inspecting parameter "::" > method "#(_)" (line 3) > method ".m" (line 3)
Method "#(_)" inside the object literal instance of "base.BaseId[Person,Customer]" (line 3)
is implemented with an expression returning "Person".
Parameter "::" has type "Person" instead of a subtype of "Customer".

Relevant code with inferred types:
User:{.m:base.BaseId[Person,Customer]->base.BaseId[Person,Customer]{#(Person):Customer->::}}
""", List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[Person,Customer] -> {::} }
"""));}
@Test void baseIdNotIdentity(){fail("""
003| MyId:base.BaseId[Customer,Person]{ #(x)->Person }
   |                                          ^^^^^^

While inspecting the file
Type declaration "MyId" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.
""", List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->Person }
"""));}
@Test void baseIdWrongReceiver(){fail("""
004| MyId:base.BaseId[base.MList[Customer],base.MList[Person]]{ #(x)->Other.cs.as{::} }
   |                                                                  ^^^^^^^^^^^^^^^

While inspecting the file
Type declaration "MyId" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Relevant code with inferred types:
Other.cs.as[imm,Person](base.BaseId[Customer,Person]{#(Customer):Person->::})
""", List.of("""
Person:{}
Customer:Person{}
Other:{ .cs: base.MList[Customer] -> base.Nope! }
MyId:base.BaseId[base.MList[Customer],base.MList[Person]]{ #(x)->Other.cs.as{::} }
"""));}
@Test void baseIdAbstractAlias(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{}
User:{ .m: MyId -> MyId{::} }
"""));}
@Test void baseIdExtraMethod(){failExt("""
In file: [###].fear

003| MyId:base.BaseId[Customer,Person]{ #(x)->x; .extra: Person -> Person }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "base.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->x; .extra: Person -> Person }
"""));}
@Test void baseIdInheritedNonIdentityBody(){failExt("""
In file: [###].fear

004| MyId:base.BaseId[Customer,Person], Forge{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "base.BaseId[_,_]".
It inherits the implementation of "#(_)" from "Forge", which does not implement "base.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "base.BaseId[_,_]".
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:{}
Forge:{ #(x: Customer): Person -> Person }
MyId:base.BaseId[Customer,Person], Forge{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as(MyId) }
"""));}
@Test void baseIdInheritedNonIdentityBodyViaAlias(){failExt("""
In file: [###].fear

005| Sub:MyId, Forge{}
   | ^^^^^^^^^^^^^^^^^

While inspecting type declaration "Sub"
Type declaration "Sub" implements "base.BaseId[_,_]".
It inherits the implementation of "#(_)" from "Forge", which does not implement "base.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "base.BaseId[_,_]".
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:{}
Forge:{ #(x: Customer): Person -> Person }
MyId:base.BaseId[Customer,Person]{}
Sub:MyId, Forge{}
"""));}
@Test void baseIdInheritedExtraMethod(){failExt("""
In file: [###].fear

004| MyId:base.BaseId[Customer,Person], Extra{ #(x)->x }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "base.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:Person{}
Extra:{ .extra: Person }
MyId:base.BaseId[Customer,Person], Extra{ #(x)->x }
"""));}
@Test void baseIdLambdaExtraMethod(){failExt("""
In file: [###].fear

003| User:{ .m: base.BaseId[Customer,Person] -> {#(x)->x; .extra: Person -> Person} }
   |                                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.BaseId[_,_]"
Object literal instance of "base.BaseId[_,_]" implements "base.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[Customer,Person] -> {#(x)->x; .extra: Person -> Person} }
"""));}
@Test void baseIdInheritedFromBaseId(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->x }
Sub:MyId{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as(Sub) }
"""));}
@Test void eqSugarNameSameAsFreshName(){ok(List.of("""
User:{ .u(n: base.Nat): base.Nat -> base.Block#.let _aeqS = {n}.return{_aeqS} }
"""));}
@Test void eqSugarNameSameAsFreshDestructName(){ok(List.of("""
Pt:{ .x: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u({.x,.y}1: Pt): base.Nat -> base.Block#.let _adiv = {x1}.return{_adiv + y1} }
"""));}
@Test void eqSugarNameSameAsFreshImplicitName(){ok(List.of("""
User:{ .u(n: base.Nat): base.F[base.Nat,base.Nat] -> base.Block#.let _aimpl = {n}.return{ {:: + _aimpl} } }
"""));}
@Test void eqSugarDestructNamesSameAsFreshName(){ok(List.of("""
Pt:{ ._aeqS: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u(p: Pt): base.Nat -> base.Block#.let {._aeqS,.y} = {p}.return{_aeqS + y} }
"""));}
@Test void eqSugarDestructNamesSameAsFreshDestructName(){ok(List.of("""
Pt:{ ._adiv: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u(p: Pt): base.Nat -> base.Block#.let {._adiv,.y}1 = {p}.let {._adiv} = {p}.return{_adiv1 + y1 + _adiv} }
"""));}
@Test void destructParameterWithHygienicResult(){ok(List.of("""
Pt:{ .x: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u[R:**]({.x,.y}1: Pt, f: mut base.MF[base.Nat,base.Nat,R]): R -> f#(x1,y1) }
"""));}
@Test void destructParametersMoreThanFourNames(){ok(List.of("""
P3:{ .a: base.Nat -> 1; .b: base.Nat -> 2; .c: base.Nat -> 3 }
User:{ .u({.a,.b,.c}1: P3, {.a,.b,.c}2: P3): base.Nat -> a1 + b1 + c1 + a2 + b2 + c2 }
"""));}
@Test void destructParameterNamesSameAsFreshName(){ok(List.of("""
Pt:{ ._aeqS: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u({._aeqS,.y}: Pt): base.Nat -> base.Block#.let z = {y}.return{_aeqS + z} }
"""));}


@Test void oldStyleAsMapsFine(){ok(List.of("""
Person:{ .name: base.Str }
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(ps: MFList[Person]): MFList[base.Str] -> ps.as{::.name} }
"""));}
@Test void oldStyleAsIdentityFine(){ok(List.of("""
Person:{}
Customer:Person{}
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(cs: MFList[Customer]): MFList[Customer] -> cs.as{::} }
"""));}
@Test void oldStyleAsWidens(){ok(List.of("""
Person:{}
Customer:Person{}
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(cs: MFList[Customer]): MFList[Person] -> cs.as{::} }
"""));}
@Test void oldStyleAsWidensWithExplicitTarg(){ok(List.of("""
Person:{}
Customer:Person{}
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(cs: MFList[Customer]): MFList[Person] -> cs.as[Person]{::} }
"""));}
@Test void expectedTypeDecidesTypeArgument(){ok(List.of("""
Person:{}
Customer:Person{}
Box[E:*]:{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
User:{ .m(c: Customer): Box[Person] -> Boxes#c }
"""));}
@Test void expectedTypeDecidesTypeArgumentOverJoin(){ok(List.of("""
Animal:{}
Dog:Animal{}
Rex:Dog{}
Fido:Dog{}
Pair[E:*]:{}
Pairs:{ #[E:*](a: E, b: E): Pair[E] -> {} }
User:{ .m: Pair[Animal] -> Pairs#(Rex, Fido) }
"""));}
@Test void expectedTypeDecidesTypeArgumentOverNamedLiterals(){ok(List.of("""
Animal:{}
Dog:Animal{}
Pair[E:*]:{}
Pairs:{ #[E:*](a: E, b: E): Pair[E] -> {} }
User:{ .m: Pair[Animal] -> Pairs#(Rex:Dog{}, Fido:Dog{}) }
"""));}
@Test void expectedTypeDecidesTypeArgumentOverWidenTo(){ok(List.of("""
Box[E:*]:{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
Family[T]:base.WidenTo[T]{}
Dir:Family[Dir]{}
North:Dir{}
User:{ .m: Box[Family[Dir]] -> Boxes#North }
"""));}
@Test void expectedTypeDecidesNestedTypeArguments(){ok(List.of("""
Person:{}
Customer:Person{}
Box[E:*]:{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
User:{ .m(c: Customer): Box[Box[Person]] -> Boxes#(Boxes#c) }
"""));}
@Test void expectedSupertypeDecidesTypeArgument(){ok(List.of("""
Person:{}
Customer:Person{}
Sup[E:*]:{}
Box[E:*]:Sup[E]{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
User:{ .m(c: Customer): Sup[Person] -> Boxes#c }
"""));}
@Test void emptyLiteralTakesSelfArgument(){ok(List.of("""
Closed[T]:{ read .close: read T }
A:Closed[A]{ .close->this }
Need:{ #(c: read Closed[A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTakesSelfArgumentAmongTwo(){ok(List.of("""
Closed[T,E:*]:{ read .close: read T }
Box[E:*]:Closed[Box[E],E]{ .close->this }
Need:{ #[E:*](c: read Closed[Box[E],E], e: E): Need -> this }
User:{ .m: Need -> Need#({}, User) }
"""));}
@Test void emptyLiteralTakesRepeatedSelfArgument(){ok(List.of("""
Closed[T,E]:{ read .close: read T }
A:Closed[A,A]{ .close->this }
Need:{ #(c: read Closed[A,A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTakesSelfArgumentAfterWiderResult(){ok(List.of("""
Sup:{}
Closed[T]:Sup{ read .close: read T }
A:Closed[A]{ .close->this }
Ids:{ #[X](a: X, b: X): X -> a }
User:{ .m(c: Closed[A]): Sup -> Ids#({}, c) }
"""));}
@Test void emptyLiteralKeepsHeadWithOnlyMutAbstract(){ok(List.of("""
Closed[T]:{ mut .close: T }
A:Closed[A]{ .close->A }
Need:{ #(c: Closed[A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTakesSelfArgumentTwice(){ok(List.of("""
Closed[T]:{ read .close: read T }
Wrap[T]:Closed[Wrap[T]]{ read .unwrap: read T }
A:Wrap[A]{ .close->this; .unwrap->this }
Need:{ #(c: read Closed[Wrap[A]]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void writtenHeadIsNotSelfArgument(){fail("""
004| User:{ .m: Need -> Need#(Closed[A]{}) }
   |        ------------------^^^^^^^^^^^-

While inspecting object literal instance of "Closed[A]" > method ".m" (line 4)
This object literal is missing a required method.
Missing: "read .close".
Required by: "Closed[_]".
Add an implementation for ".close" inside the object literal.
""", List.of("""
Closed[T]:{ read .close: read T }
A:Closed[A]{ .close->this }
Need:{ #(c: read Closed[A]): Need -> this }
User:{ .m: Need -> Need#(Closed[A]{}) }
"""));}
@Test void emptyLiteralNoSelfArgument(){fail("""
004| User:{ .m: Need -> Need#{} }
   |        -----------------^^

While inspecting object literal instance of "read Closed[B]" > method ".m" (line 4)
This object literal is missing a required method.
Missing: "read .close".
Required by: "Closed[_]".
Add an implementation for ".close" inside the object literal.
""", List.of("""
Closed[T]:{ read .close: read T }
B:{}
Need:{ #(c: read Closed[B]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTwoSelfArguments(){fail("""
005| User:{ .m: Need -> Need#{} }
   |        -----------------^^

While inspecting object literal instance of "read Closed[A,B]" > method ".m" (line 5)
This object literal is missing a required method.
Missing: "read .close".
Required by: "Closed[_,_]".
Add an implementation for ".close" inside the object literal.
""", List.of("""
Closed[T,E]:{ read .close: read T }
A:Closed[A,B]{ .close->this }
B:Closed[A,B]{ .close->A }
Need:{ #(c: read Closed[A,B]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralSelfArgumentStillAbstract(){fail("""
004| User:{ .m: Need -> Need#{} }
   |        -----------------^^

While inspecting object literal instance of "read A" > method ".m" (line 4)
This object literal is missing a required method.
Missing: "imm .name".
Required by: "A".
Add an implementation for ".name" inside the object literal.
""", List.of("""
Closed[T]:{ read .close: read T }
A:Closed[A]{ .name: A }
Need:{ #(c: read Closed[A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}

/*The five tests below are the minimized shapes of every place base stops compiling if
InjectionSteps.nextMStarOp stops meeting a method's declared return type with the type of its
body, that is if
  var ret= meet(m.sig().ret().get(), e.t());
becomes
  var ret= m.sig().ret().get();*/

@Test void blockLetInfersItsTypeFromTheLambdaBody(){ok(List.of("""
use base.MF as MF; use base.Bool as Bool; use base.True as True;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
Amount: { +(o: Amount): Amount -> this; .lt(o: Amount): Bool -> True }
User: {
  .m(a: Amount, b: Amount): Amount -> Blocks#
    .let sum = {a + b}
    .return { sum.lt(b).if {
        .then -> sum + b;
        .else -> sum
      }};
  }
"""));}
/*Minimizes base.Math.euclideanMod in math.fear. "X" of ".let" appears only inside the "mut MF[X]"
parameter, so nothing at the use site can decide it and the lambda body is the only source. The
".if" in the continuation matters: with a plain ".return {sum}" the requirement on the block's own
result reaches "sum" and X is decided anyway; once "sum" is only ever a receiver inside the
continuation, dropping the meet leaves "iso MF[InferUnknown]".*/

@Test void thenElseInfersItsTypeFromTheBranchBodies(){ok(List.of("""
use base.Bool as Bool; use base.Void as Void; use base.Nope as Nope;
Seq: { #[A:**,R:**](a: A, res: R): R -> res }
User: {
  .m[R:iso,imm,mut,read](r: R, b: Bool): R -> Seq#(b?{.then->Void; .else->Nope!}, r);
  }
"""));}
/*Minimizes base._IdOrErr in var.fear. Same reason as the test above but through "?" instead of
".let": "R" of "base.ThenElse[R]" is only the return type of the branches, and "Seq" discards its
first argument, so the branch bodies are the only source of R.*/

@Test void identityLambdaInfersItsKeyTypeFromItsOwnParameter(){ok(List.of("""
use base.Nope as Nope;
Ord[K]: {}
By[T,K]: {
  #(x: read T): read Ord[K];
  .hide: By[T,K] -> this;
  }
Key: Ord[Key] {}
Box[T]: {}
Mk: { #[T,K](by: By[T,K], t: T): Box[T] -> Nope! }
Caller: { .go(x: Key): Box[Key] -> Mk#({::}, x) }
"""));}
/*Minimizes the "Maps#({::},k1,e1.info)" calls of base.Infos in datatypes/info/info.fear. "T" of "By"
comes from the use site, "K" does not: it can only come from the body of "{::}", which is the
parameter of the very method whose return type we are deciding. Dropping the meet leaves the head
of "{::}" at "By[InferUnknown,InferUnknown]" while its method table is refined with "Key", and the
literal is then internally inconsistent: this one fails the "mostSpecificByOrigin" assert inside
TypeSystem.methodTableOk rather than reporting a user error.*/

@Test void blockLetOfAMutResultCannotBePromotedThroughACapturedMut(){fail("""
011|   mut .take(s: mut Set[E], e: E): Opt[E] -> Blocks#
012|     .let o = {s.opt(e)}
013|     .return {o};
   |              ^

While inspecting parameter "o" > method "#" (line 13) > method "#(_,_)" (line 11) > method ".take(_,_)" (line 11)
Method "#" inside the object literal instance of "mut MF[Opt[E]]" (line 13)
is implemented with an expression returning "mut Opt[E]".
Parameter "o" has type "mut Opt[E]" instead of a subtype of "imm Opt[E]".

Name "_aeqS" is a parameter added by the desugaring of "=": ".let x = {a}.return {b}" stands for ".let({a}, {x, _aeqS -> _aeqS.return {b}})".

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
_#[imm,Opt[E]].let[mut,mut Opt[E]](mut MF[_]{...},mut Continuation[mut Opt[E],Opt[E]]{mut #(o:mut Opt[E],_aeqS:mut Block[Opt[E]]):Opt[E]->_aeqS.return[mut](mut MF[Opt[E]]{mut #:Opt[E]->o})})
""", List.of("""
use base.MF as MF;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
Opt[E:imm]: {}
Set[E:imm]: { mut .opt(e: E): mut Opt[E] -> {} }
User[E:imm]: {
  mut .take(s: mut Set[E], e: E): Opt[E] -> Blocks#
    .let o = {s.opt(e)}
    .return {o};
  }
"""));}

@Test void blockLetTypeCarriesTheClassTypeParameterIntoTheLambda(){ok(List.of("""
use base.MF as MF; use base.Nat as Nat; use base.Ten as Ten;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
Set[E:imm]: { .distinct: Set[E] -> this }
User[E:imm]: {
  .m(other: Set[E]): Nat -> Blocks#
    .let other2 = {other.distinct}
    .return {Ten};
  }
"""));}
/*Minimizes base.Set.difference in datatypes/collections/sets/set.fear. X is again only decided by
the lambda body, but the body's type mentions "E", so the failure is not the one of
blockLetInfersItsTypeFromTheLambdaBody: the literal generated for "{other.distinct}" is given the
head "iso MF[InferUnknown]", which mentions no generic type parameter, so the fresh declaration is created
without binders and capturing "other" is then reported as a capture error.*/


@Test void overridingErrorsAreReportedInDeclarationOrder(){fail("""
004| B: A { .m1: P -> P; .m2: P -> P }
   | -------^^^^^^^^^^^---------------

While inspecting type declaration "B"
Invalid method signature for "B.m1".
The method ".m1" returns type "P".
But "A.m1" returns type "Q", which is not a supertype of "P".
It is instead a subtype: you are weakening the result instead of strengthening it.

Relevant code with inferred types:
B:A{.m1:P->P;.m2:P->P}
""", List.of("""
P:{}
Q:P{}
A: { .m1: Q; .m2: Q }
B: A { .m1: P -> P; .m2: P -> P }
"""));}
/*Both ".m1" and ".m2" are bad overrides, and litOk reports whichever method key it visits first.
litOk groups the result of Sources.collect by method key in a LinkedHashMap, so that order is fixed
from run to run. A HashMap keyed on a record holding an RC would not do: enum hashCodes are identity hashCodes, the
order would depend on the JVM's allocation sequence, and an unrelated change elsewhere in the run
would silently change which of the two errors the user is shown.*/

@Test void miniClassDoesntCauseCompilationProblem(){ok(List.of("""
use base.Opt as Opt;
use base.Opts as Opts;
use base.F as F;

TestClass[T]: {
  .opt: mut Opt[T];
  .example[R:*](f: F[R]): mut Opt[R] -> this.opt.match {
    .some _ -> Opts#(f#);
    .empty -> {};
    };
  }
"""));}
@Test void anonLiteralWithRcOverloadsAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Ids:{ #[T:*](t: T): read T -> t }
User:{ .f: read base.Opt[Foo] -> Ids#({ .match m -> m.empty }) }
"""));}
@Test void anonLiteralAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Sup:{ .g: Foo }
Ids:{ #[T:*](t: T): read T -> t }
User:{ .f: read Sup -> Ids#({ .g -> Foo }) }
"""));}
@Test void inferenceLimit_anonLiteralCapturingMutAgainstTypeArgumentWithoutRc(){fail("""
004| User:{ .f(s: mut Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
   |        ---------------------------------------------~~~~~~~~^---

While inspecting parameter "c" > method ".run" (line 4) > method ".f(_,_)" (line 4)
Parameter "c" has type "mut Foo".
Parameter "c" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "Sup" (line 4).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
"""));}
@Test void mutLiteralCapturingMutAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Sup, c: mut Foo): Foo -> Two#(s, mut Sup{ .run -> c }) }
"""));}
@Test void inferenceLimit_anonLiteralWithRcOverloadsCapturingMutAgainstTypeArgumentWithoutRc(){fail("""
004| User:{ .f(s: mut Box, c: mut Foo): Foo -> Two#(s, { .get -> c }) }
   |        ---------------------------------------------~~~~~~~~^---

While inspecting parameter "c" > method ".get" (line 4) > method ".f(_,_)" (line 4)
Parameter "c" has type "mut Foo".
Parameter "c" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "Box" (line 4).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Foo:{}
Box:{ mut .get: mut Foo; read .get: read Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Box, c: mut Foo): Foo -> Two#(s, { .get -> c }) }
"""));}
@Test void mutLiteralWithRcOverloadsCapturingMutAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Box:{ mut .get: mut Foo; read .get: read Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Box, c: mut Foo): Foo -> Two#(s, mut Box{ .get -> c }) }
"""));}
@Test void inferenceLimit_anonLiteralCapturingMutAgainstTypeArgumentFromIsoArgument(){fail("""
004| User:{ .f(s: iso Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
   |        ---------------------------------------------~~~~~~~~^---

While inspecting parameter "c" > method ".run" (line 4) > method ".f(_,_)" (line 4)
Parameter "c" has type "mut Foo".
Parameter "c" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "Sup" (line 4).
Capture an immutable copy instead, or move this use outside the object literal.
""", List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: T, b: T): Foo -> Foo }
User:{ .f(s: iso Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
"""));}
@Test void mutLiteralCapturingMutAgainstTypeArgumentFromIsoArgument(){ok(List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: T, b: T): Foo -> Foo }
User:{ .f(s: iso Sup, c: mut Foo): Foo -> Two#(s, mut Sup{ .run -> c }) }
"""));}

@Test void isoLiteralCanUseItsSelfName(){ok(List.of("""
Counter:{ mut .inc: mut Counter; read .get: base.Nat; mut .inc2: mut Counter }
Make:{ #: iso Counter -> iso Counter{'self
  mut .inc: mut Counter -> self;
  read .get: base.Nat -> 0;
  mut .inc2: mut Counter -> self.inc[mut].inc[mut];
  } }
"""));}
@Test void isoLiteralStillDropsCapturedIso(){ok(List.of("""
A:{}
Box:{ read .get: A; }
Make:{ #(a:iso A): iso Box -> iso Box{ read .get: A -> a } }
"""));}
@Test void isoLiteralSelfIsReadInReadMethod(){fail("""
002| Make:{ #: iso Counter -> iso Counter{'self
003|   mut .inc: mut Counter -> self;
004|   read .get: read Counter -> self.inc[mut];
   |   ---------------------------^^^^~~~~~~~~~
005|   } }

While inspecting method ".get" (line 4) > method "#" (line 2)
This call to method "mut Counter.inc" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".
The capability of the methods changes the type of parameter "self":
- "mut Counter" becomes "read Counter" inside the "read" method ".get" (line 4).

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Relevant code with inferred types:
self.inc[mut]
""", List.of("""
Counter:{ mut .inc: mut Counter; read .get: read Counter }
Make:{ #: iso Counter -> iso Counter{'self
  mut .inc: mut Counter -> self;
  read .get: read Counter -> self.inc[mut];
  } }
"""));}
@Test void isoLiteralStillPromotesUnnamedMutLiteral(){ok(List.of("""
Counter:{ read .get: base.Nat }
Make:{ #: iso Counter -> mut Counter{ read .get: base.Nat -> 0 } }
"""));}
@Test void isoLiteralPromotesSelfNamedMutLiteral(){ok(List.of("""
Counter:{ mut .inc: mut Counter; read .get: base.Nat }
Make:{ #: iso Counter -> mut Counter{'self
  mut .inc: mut Counter -> self;
  read .get: base.Nat -> 0;
  } }
"""));}
@Test void isoLiteralPromotesSelfNamedImmLiteral(){ok(List.of("""
A:{ read .me: imm A }
Make:{ #: iso A -> imm A{'self read .me: imm A -> self } }
"""));}
@Test void selfNameDeadCode(){fail("""
002| Make:{ #: A -> A{'self read .get: base.Nat -> 0 } }
   |        --------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "A" > method "#" (line 2)
The self name "self" is dead code.
No method of the object literal instance of "A" uses it.
Remove "'self" from the object literal.

Relevant code with inferred types:
A{'self read .get:base.Nat->0}
""", List.of("""
A:{ read .get: base.Nat }
Make:{ #: A -> A{'self read .get: base.Nat -> 0 } }
"""));}
@Test void selfNameUsedOnlyInNestedLiteral(){ok(List.of("""
A:{ read .get: A }
Make:{ #: A -> A{'self read .get: A -> A{ read .get: A -> self } } }
"""));}
@Test void mutLiteralCapturingIsoIsPromotedToIso(){ok(List.of("""
A:{}
Box:{ read .get: A; }
Make:{ #(a:iso A): iso Box -> mut Box{ read .get: A -> a } }
"""));}
@Test void inheritedMethodSpelledWithAndWithoutRedundantRcOnTypeVariable(){ok(List.of("""
M[R:**]:{ mut .a: R; mut .b: R -> this.a; }
TM[K]:{ read #(x: K): mut M[K] }
MM:{ #[K]: TM[K] -> {x -> { .a -> x }} }
"""));}
@Test void inheritedMethodSpelledWithAndWithoutRedundantMutOnTypeVariable(){ok(List.of("""
M[R:**]:{ mut .a: R; mut .b: R -> this.a; }
TM[K:mut]:{ read #(x: K): mut M[K] }
MM:{ #[K:mut]: TM[K] -> {x -> { .a -> x }} }
"""));}
@Test void lambdaParameterTypedFromExplicitTypeArgumentOfReceiverCall(){ok(List.of("""
Fn[A:*,R:*]:{ read #(a: A): R }
TF[E:*]:{ }
L[E:*]:TF[E]{ }
Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }
Fls:{ #[R:*](r: R): mut Fl[R]; }
Use:{ #[E:*](fls: Fls, xs: mut L[E]): mut Fl[E] -> fls#[read TF[E]](xs).g[E]{c -> c} }
"""));}
@Test void explicitTypeArgumentKeepsItsRcAgainstTheArgument(){ok(List.of("""
Fn[A:*,R:*]:{ read #(a: A): R }
TF[E:*]:{ }
Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }
Fls:{ #[R:*](r: R): mut Fl[R]; }
Use:{ #[E:*](fls: Fls, xs: mut TF[E]): mut Fl[E] -> fls#[read TF[E]](xs).g[E]{c -> c} }
"""));}
@Test void lambdaParameterTypedFromReceiverTypeWhenReceiverIsParameter(){ok(List.of("""
Fn[A:*,R:*]:{ read #(a: A): R }
TF[E:*]:{ }
L[E:*]:TF[E]{ }
Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }
Use:{ #[E:*](fl: mut Fl[read TF[E]]): mut Fl[E] -> fl.g[E]{c -> c} }
"""));}@Test void inferredTypeArgumentOfNestedCallFollowsExpectedType(){ok(List.of("""
C:{}
L[E:*]:{}
Ls:{ #[E:*](e: E): mut L[E] -> {} }
User:{ .nested(css: L[L[C]]): C -> C; .t: C -> this.nested(Ls#(Ls#(C))) }
"""));}
@Test void argFromObjectLiteral_mutHParam_hintToWriteMutLiteral(){fail("""
005|   .f:B->
006|     Need#(read A{});
   |     ------^^^^^^^^-

While inspecting method ".f" (line 5)
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
Object literal is of type "read A" instead of a subtype of "mutH A".
Write "mut A" if you need a "mut" object literal (needed to satisfy the "mutH" requirement).

Type required by each promotion:
[###]
""", List.of("""
B:{}
Need:{ #(a:mutH A):B->B{} }
A:{ mut .foo:A}
User:{
  .f:B->
    Need#(read A{});
}
"""));}
@Test void bodyFromObjectLiteral_wrongNominal_noHintToChangeRC(){fail("""
004|   .f:mut A->
005|     read C{};
   |     ^^^^^^^^

While inspecting object literal instance of "read C" > method ".f" (line 4)
The body of method ".f" of type declaration "User" is an expression returning "read C".
Object literal is of type "read C" instead of a subtype of "mut A".

Relevant code with inferred types:
User:{.f:mut A->read C}
""", List.of("""
A:{ mut .foo:A}
C:{ mut .bar:C}
User:{
  .f:mut A->
    read C{};
}
"""));}
@Test void tsWidenRedundantlyListed(){ok(List.of("""
Sup:base.WidenTo[Target]{}
Target:Sup, base.WidenTo[Target]{}
"""));}
@Test void tsWidenRedundantlyListedNested(){ok(List.of("""
Sup:base.WidenTo[Target]{}
Target:Sup{}
User:{ #:Sup->N:base.WidenTo[Target], Sup{} }
"""));}
@Test void tsSupertypesCollapsingUnderInstantiation(){ok(List.of("""
Foo[X:imm]:{}
S:{}
A[X:imm]:Foo[X],Foo[S]{ .m:S; }
User:{ #:A[S]->{ .m->S{} } }
"""));}
@Test void tsSupertypesCollapsingUnderInstantiationSpelledDifferently(){ok(List.of(
  "Foo[X:*]:{} S:{} A[X:*,Y:*]:Foo[X],Foo[Y]{ .m:S; } User:{ #[Z:imm]:A[Z,imm Z]->{ .m->S{} } }"));}
@Test void tsSupertypesCollapsingUnderInstantiationSpelledDifferentlyTyped(){ok(List.of(
  "Foo[X:*]:{} S:{} A[X:*,Y:*]:Foo[X],Foo[Y]{ .m:S; } User:{ #[Z:imm]:A[Z,imm Z]->A[Z,imm Z]{ .m->S{} } }"));}
@Test void tsSupertypesCollapsingUnderInstantiationSpelledDifferentlyReadImm(){ok(List.of(
  "Foo[X:**]:{} S:{} A[X:**,Y:**]:Foo[X],Foo[Y]{ .m:S; } User:{ #[Z:imm]:A[Z,read/imm Z]->{ .m->S{} } }"));}
@Test void nestedSelfDispatchUsesMethodCapability(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; .m2: A }
User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> self.m1 } }
"""));}
@Test void nestedSelfDispatchUsesReadMethodCapability(){ok(List.of("""
A:{ read .m1: read A; mut .m1: mut A; read .m2: read A }
User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> self.m1 } }
"""));}
@Test void nestedSelfCapturedDeeperUsesMethodCapability(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; .m2: mut G }
G:{ mut .get: A }
User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> mut G{ .get -> self.m1 } } }
"""));}
@Test void isoNestedSelfCapturedDeeperIsMut(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; mut .m2: mut G }
G:{ mut .get: mut A }
User:{ #: iso A -> iso B:A{'self .m1 -> self; .m2 -> mut G{ .get -> self.m1 } } }
"""));}
@Test void genericArgumentsJoinToTheSupertype(){ok(List.of("""
A:{} Z:A{}
U:{ .both[T](a: T, b: T): T -> a; .use(a: A, z: Z): A -> this.both(a, z) }
"""));}
@Test void genericArgumentsJoinToTheSupertypeInEitherOrder(){ok(List.of("""
A:{} Z:A{}
U:{ .both[T](a: T, b: T): T -> a; .use(a: A, z: Z): A -> this.both(z, a) }
"""));}
@Test void genericArgumentsJoinMutAndImmToRead(){ok(List.of("""
A:{}
U:{ .both[T:*](a: T, b: T): T -> a; .use(m: mut A, i: imm A): read A -> this.both(m, i) }
"""));}
@Test void genericArgumentFromALiteralJoinsToo(){ok(List.of("""
A:{} Z:A{}
U:{ .app[T](f: base.F[T], x: T): T -> x; .use(a: A, z: Z): A -> this.app({ z }, a) }
"""));}
@Test void siblingsJoinToTheExpectedSupertypeA(){ok(List.of("""
A:{} B:{} Y:A,B{} Z:A,B{}
U:{ .both[T](a: T, b: T): T -> a; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void siblingsJoinToTheExpectedSupertypeB(){ok(List.of("""
A:{} B:{} Y:A,B{} Z:A,B{}
U:{ .both[T](a: T, b: T): T -> a; .use(y: Y, z: Z): B -> this.both(y, z) }
"""));}
@Test void siblingsWithoutContextCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
   |                                                          ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
"T" could be "A" or "B": each is a supertype of "Y" and "Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "this.both[A](y, z)".
""", List.of("""
A:{} B:{} Y:A,B{} Z:A,B{}
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void siblingsWithOneCommonSupertypeInferIt(){ok(List.of("""
A:{ .k: A -> this } Y:A{} Z:A{}
U:{ .both[T](a: T, b: T): T -> a; .use(y: Y, z: Z): A -> this.both(y, z).k }
"""));}
@Test void unrelatedTypesCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
   |                                                          ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.both[Type1](y, z)".
""", List.of("""
A:{} Y:{} Z:{}
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void methodBodiesOfUnrelatedTypesCannotBeInferred(){failWf("""
003| U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
   |                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.ThenElse[_]"
The generic type argument "R" of "base.ThenElse[_]" is inferred from the method bodies, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "base.ThenElse[Type1]{...}".
""", List.of("""
A:{} Y:{} Z:{}
Sink:{ #[T](t: T): A -> A }
U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
"""));}
@Test void methodBodiesWithTwoCommonSupertypesCannotBeInferred(){failWf("""
003| U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
   |                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.ThenElse[_]"
The generic type argument "R" of "base.ThenElse[_]" is inferred from the method bodies, but they disagree: some need "Y", some need "Z".
"R" could be "S1" or "S2": each is a supertype of "Y" and "Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "base.ThenElse[S1]{...}".
""", List.of("""
A:{} S1:{} S2:{} Y:S1,S2{} Z:S1,S2{}
Sink:{ #[T](t: T): A -> A }
U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
"""));}
@Test void unconstrainedTypeArgumentInsideATypeArgumentIsVoidWithinItsBound(){ok(List.of("""
Box[X:mut]:{ .k: Box[X] -> this }
Mk:{ #[X:mut]: Box[X] -> Box[X] }
Block:{ #[A](a: A): base.Void -> {} }
User:{ .go: base.Void -> Block#(Mk#) }
"""));}
@Test void unconstrainedTypeArgumentInsideATypeArgumentIsVoidWithinItsReadMutBound(){ok(List.of("""
Box[X:read,mut]:{ .k: Box[X] -> this }
Mk:{ #[X:read,mut]: Box[X] -> Box[X] }
Block:{ #[A](a: A): base.Void -> {} }
User:{ .go: base.Void -> Block#(Mk#) }
"""));}
@Test void emptyLiteralReceiverWithASealedExpectedTypeIsATypeError(){fail("""
001| App:{ .m: base.Nat -> {}.a }
   |       ----------------~~^^

While inspecting method ".m" (line 1)
This call to method ".a" cannot typecheck.
Method ".a" is not declared on "{...}".
Object literal "{...}" does not have any methods.

Relevant code with inferred types:
{}.a
""", List.of("""
App:{ .m: base.Nat -> {}.a }
"""));}
@Test void literalReceiverWithAMethodAndASealedExpectedTypeIsATypeError(){fail("""
001| App:{ .m: base.Nat -> {.b:base.Void->base.Void;}.a }
   |       ----------------~~~~~~~~~~~~~~~~~~~~~~~~~~^^

While inspecting method ".m" (line 1)
This call to method ".a" cannot typecheck.
Method ".a" is not declared on "{...}".

Available methods on "{...}":
- .b:base.Void

Relevant code with inferred types:
{.b:base.Void->base.Void}.a
""", List.of("""
App:{ .m: base.Nat -> {.b:base.Void->base.Void;}.a }
"""));}
@Test void typesWithDifferentInvariantArgumentsCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
   |                                                          ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.both[Type1](y, z)".
""", List.of("""
A:{} B:{} Sup[T]:{ .k: T } Y:Sup[A]{ .k -> A } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void aTypeAndASubtypeWithDifferentInvariantArgumentsCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Sup[A], z: Z): A -> this.both(y, z) }
   |                                                               ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Sup[A]", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.both[Type1](y, z)".
""", List.of("""
A:{} B:{} Sup[T]:{ .k: T } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Sup[A], z: Z): A -> this.both(y, z) }
"""));}
@Test void typesWithDifferentInvariantArgumentsJoinToACommonSupertypeAbove(){ok(List.of("""
A:{} B:{} Top:{} Sup[T]:Top{ .k: T } Y:Sup[A]{ .k -> A } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}@Test void aTypeAndASubtypeWithDifferentInvariantArgumentsJoinToACommonSupertypeAbove(){ok(List.of("""
A:{} B:{} Top:{} Sup[T]:Top{ .k: T } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Sup[A], z: Z): A -> this.both(y, z) }
"""));}
@Test void lambdaParameterCapturedBeforeItsOtherUseIsInferredAsWhenCapturedAfter(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mut A): A -> a.m }
Imm:{ #(a: A): A -> a }
G:{ imm #: A }
Two:{ #[X:*,Y:*](a: X, b: Y): Y -> b }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: A -> Ap#{x -> Two#(mut G{ # -> Imm#x }, Mut#x)} }
"""));}
@Test void lambdaParameterCapturedAfterItsOtherUseIsInferredFromTheOtherUse(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mut A): A -> a.m }
Imm:{ #(a: A): A -> a }
G:{ imm #: A }
Two:{ #[X:*,Y:*](a: X, b: Y): X -> a }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: A -> Ap#{x -> Two#(Mut#x, mut G{ # -> Imm#x })} }
"""));}
@Test void lambdaParameterOnlyCapturedInAnImmMethodIsImm(){ok(List.of("""
A:{ mut .m: A -> A }
Imm:{ #(a: A): A -> a }
G:{ imm #: A }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: mut G -> Ap#{x -> mut G{ # -> Imm#x }} }
"""));}
@Test void lambdaParameterOnlyCapturedInAMutMethodIsMut(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mut A): A -> a.m }
G:{ mut #: A }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: mut G -> Ap#{x -> mut G{ # -> Mut#x }} }
"""));}
@Test void deepWrittenSupertype(){ok(List.of("A[X:**]:{}\nB:"+"A[".repeat(99)+"B"+"]".repeat(99)+"{}\n"));}
@Test void parameterHashCollidingWithThis(){ok(List.of("""
A:{ .id[Y:**](y:Y):Y -> y; .u(tiJs:A):A -> this.id(tiJs) }
"""));}
@Test void abstractParameterNameNotReusedAsFreshName(){ok(List.of("""
use base.F as F;
A:{ .m(_aimpl:A):A; .k(f:F[A,A]):A; .z:A -> this.k{::.m(this)} }
"""));}
static String box(int n, String in){ return "Box[".repeat(n)+in+"]".repeat(n); }
@Test void supertypeImpliedByAnotherSupertype(){ok(List.of("""
C:{ .m[X](x:X):X; }
B:C{}
A[X]:C,B{}
"""));}
@Test void deepInstantiatedParameter(){ok(List.of("""
N:{}
Box[T:*]:{}
A:{ .mk[T:*]: Box[T] -> Box[T]; .use[S:*](s: Box[S]): N -> N; .go: N -> this.use[imm,D](this.mk[imm,D]) }
""".replace("D", box(98, "N"))));}
@Test void deepInstantiatedParameterNotASubtype(){fail("""
[###]This call to method "Take#(_)" cannot typecheck.
Argument 1 has type "Box[Y]".
That is not a subtype of "Box[[###]
""", List.of("""
N:{}
Box[X]:{}
Take:{ #[Y](c: Box[Y]): N -> N }
Use:{ .m[Y](c: Box[Y]): N -> Take#[D](c) }
""".replace("D", box(98, "N"))));}
@Test void deepCallResult(){fail("""
002| U[X]:{ .m(k: K[[###]]): Box[Box[X]] -> k.get }
   |        [###]^^^^^

While inspecting method call ".get" > method ".m(_)" (line 2)
The body of method ".m(_)" of type declaration "U[_]" is an expression returning "Box[Box[Box[[###]".
Method call "K[_].get" has type "Box[Box[Box[[###]" instead of a subtype of "Box[Box[X]]".

Relevant code with inferred types:
U[X]:{.m(k:K[[###]]):Box[Box[X]]->k.get}
""", List.of("""
A:{} Box[X]:{} K[X]:{ .get: Box[Box[X]] }
U[X]:{ .m(k: K[D]): Box[Box[X]] -> k.get }
""".replace("D", box(97, "A"))));}
@Test void deepArgumentTypeIsNotWritten(){ok(List.of("""
N:{}
Box[X]:{}
U[S]:{ .use(s: Box[Box[S]]): N }
K[X]:{ .get: Box[Box[X]] }
Use:{ .go(u: U[D], k: K[D]): N -> u.use(k.get) }
""".replace("D", box(97, "N"))));}
@Test void deepInferredTypeArgumentFromAnotherArgument(){ok(List.of("""
N:{}
Box[X]:{}
Take:{ #[Y](a: Y, c: Box[Box[Y]]): N -> N }
W[X]:{ .get: Box[Box[X]] }
Use:{ .m(a: D, w: W[D]): N -> Take#(a, w.get) }
""".replace("D", box(97, "N"))));}
@Test void deepImpliedSupertype(){ok(List.of("""
N:{}
Box[X]:{}
C[X]:{}
B[X]:C[Box[X]]{}
A:B[D]{}
""".replace("D", box(97, "N"))));}
@Test void deepVoidDefault(){ok(List.of("""
N:{}
Box[X]:{}
Mk:{ #[T]: D -> {} }
Ign:{ #[K](k: K): N -> N }
Use:{ .m: N -> Ign#(Mk#) }
""".replace("D", box(99, "T"))));}
@Test void deepCallResultIsNotWritten(){ok(List.of("""
N:{}
Box[X]:{ .get: X }
W:{ #[T](t: T): Box[T] -> { .get -> t } }
Use:{ .m(x: D): D -> W#(x).get }
""".replace("D", box(98, "N"))));}
@Test void deepInheritedSupertypeAcrossDeclarations(){ok(List.of("N:{}\nBox[X]:{}\nB0[X]:{}\n"+IntStream.rangeClosed(1, 99).mapToObj(i -> "B"+i+"[X]:B"+(i-1)+"[Box[X]]{}\n").collect(Collectors.joining())));}
@Test void deepInheritedSignature(){ok(List.of("""
N:{}
Box[X]:{}
B[X]:{ .m(x: Box[Box[X]]): N }
A:B[D]{}
""".replace("D", box(97, "N"))));}
@Test void deepInferredHead(){ok(List.of("""
N:{}
Box[X]:{}
K[X]:{ .get: Box[Box[X]] }
Foo[X]:{ .m(x: X): X }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go(k: K[D]): N ->
  Take#{ .m(x) -> k.get } }
""".replace("D", box(97, "N"))));}
@Test void deepLiteralMethod(){ok(List.of("""
N:{}
Box[X]:{}
Foo[X]:{ .id: X; .m(x: Box[Box[X]]): N }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go(d: D): N ->
  Take#{ .id -> d; .m(x) -> N } }
""".replace("D", box(97, "N"))));}
@Test void deepSupertypeWalkedByTheTypeChecker(){ok(List.of("""
A:{} Top:{} Box[X]:Top{} W[X]:Box[Box[X]]{}
U:{ .m(w: W[D]): Top -> w }
""".replace("D", box(97, "A"))));}
@Test void typeGrowsForever(){failWf("""
006| Use:{ .go: N -> Take#{ .m(x) -> Wrap#(x) } }
   |                      ^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Foo[_]"
Type inference finds no type for object literal instance of "Foo[_]".
Each round of inference nests its type one level deeper, as "Foo[Box[Box[...]]]"; it would grow without bound.
""", List.of("""
N:{}
Box[X]:{}
Wrap:{ #[Y](y: Y): Box[Y] -> {} }
Foo[X]:{ .m(x: X): X }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go: N -> Take#{ .m(x) -> Wrap#(x) } }
"""));}
@Test void unrelatedTypesInsideAnInferredTypeArgument(){failWf("""
002| U:{ .mk[R]: R; .two[T](a: T, b: T, c: Box[T]): A; .use(y: Y, z: Z): A -> this.two(y, z, this.mk) }
   |                                                                          ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".two(_,_,_)"
The generic type argument "T" of ".two" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.two[Type1](y, z, this.mk)".
""", List.of("""
A:{} Y:{} Z:{} Box[X]:{}
U:{ .mk[R]: R; .two[T](a: T, b: T, c: Box[T]): A; .use(y: Y, z: Z): A -> this.two(y, z, this.mk) }
"""));}
@Test void unrelatedCandidatesNestedInInferredTypeArgument(){failWf("""
007| User:{ .go(a: A, b: B): A -> Ign#(Mk#.m(a, b)) }
   |                              ^^^^^^^^^^^^^^^^^

While inspecting method call "#(_)"
The generic type argument "T" of "#" is inferred from the arguments, but they disagree: some need "Bar[A]", some need "Bar[B]".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "Ign#[Type1](Mk#.m(a, b))".
""", List.of("""
A:{}
B:{}
Bar[X]:{}
Foo[X]:{ .m(a: X, b: X): Bar[X] -> {} }
Mk:{ #[X]: Foo[X] -> {} }
Ign:{ #[T](t: T): A -> A }
User:{ .go(a: A, b: B): A -> Ign#(Mk#.m(a, b)) }
"""));}
@Test void unrelatedTypesInsideAnInferredLiteral(){failWf("""
006| Use:{ .go(y: Y, z: Z): A -> Take#{ Left.choose(y, z) } }
   |                                    ^^^^^^^^^^^^^^^^^

While inspecting method call ".choose(_,_)"
The generic type argument "V" of ".choose" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "Left.choose[Type1](y, z)".
""", List.of("""
A:{} Y:{} Z:{}
Fork:{ .choose[V](l: V, r: V): V }
Left:Fork{ l,r -> l }
F[R]:{ #: R }
Take:{ #[R](f: F[R]): A -> A }
Use:{ .go(y: Y, z: Z): A -> Take#{ Left.choose(y, z) } }
"""));}
@Test void unrelatedTypesInsideALetValue(){failWf("""
004| Use:{ .go: base.Void -> base.Block#.let x= {Left.choose("Hello", TankNN)}.return{base.Void} }
   |                                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".choose(_,_)"
The generic type argument "Val" of ".choose" is inferred from the arguments, but they disagree: some need "base.Str", some need "TankNN".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in `Left.choose[Type1]("Hello", TankNN)`.
""", List.of("""
Fork:{ .choose[Val](leftVal: Val, rightVal: Val): Val }
Left:Fork{ l,r -> l }
Tank:{} TankNN:Tank{}
Use:{ .go: base.Void -> base.Block#.let x= {Left.choose("Hello", TankNN)}.return{base.Void} }
"""));}
@Test void isoReceiverOverloadFollowsTheExpectedResult(){ok(List.of("""
S:{ read .m: read S -> this; mut .m: mut S -> this }
A:{ .k(s: iso S): mut S -> s.m; .j(s: iso S): read S -> s.m; .i(s: iso S): imm S -> s.m }
"""));}
@Test void receiverLiteralDeclaringTheCalledMethodKeepsItsOwnType(){ok(List.of("""
A: {.m: A}
D: { .k: A -> {.size: A -> D.k}.size }
"""));}
@Test void readNamedLiteralWithoutMutMethodsIsPromotedToIso(){ok(List.of("""
S:{ read .m: read S }
A:{ .k: imm S -> read S{'s .m -> s}; .j: iso S -> imm S{'s .m -> s} }
"""));}
@Test void promotedNamedLiteralKeepsTheWrittenSelfCapability(){ok(List.of("""
S:{ read .m: base.F[S] }
A:{ .k: iso S -> imm S{'s .m -> { s } } }
"""));}
@Test void captureFreeNestedSelfIsImmInEveryMethod(){ok(List.of("""
A:base.CaptureFree{ mut .bar: A }
User:{ #: mut A -> mut B:A{'self mut .bar: A -> self } }
"""));}
@Test void captureFreeTopLevelThisIsImmInEveryMethod(){ok(List.of("""
A: base.CaptureFree, base.F[A]{ #: A -> this }
B: base.CaptureFree{ read .me: imm A -> A; mut .self: imm B -> this }
"""));}
@Test void captureFreeTopLevelThisInMutMethodInfersTheImmOverload(){ok(List.of("""
A:base.CaptureFree{
  imm .bar: A -> this;
  mut .bar: A -> this;
  mut .foo: A -> this.bar;
  }
"""));}
@Test void captureFreeTopLevelThisInMutMethodWrittenImmOverload(){ok(List.of("""
A:base.CaptureFree{
  imm .bar: A -> this;
  mut .bar: A -> this;
  mut .foo: A -> this.bar[imm];
  }
"""));}
@Test void captureFreeTopLevelThisInMutMethodInfersImmLetType(){ok(List.of("""
A:base.CaptureFree{ mut .foo: A -> base.Block#.let x= {this} .return {x} }
"""));}
@Test void captureFreeTopLevelThisInMutMethodWrittenLetType(){ok(List.of("""
A:base.CaptureFree{ mut .foo: A -> base.Block#.let[A] x= {this} .return {x} }
"""));}
@Test void captureFreeTopLevelThisInImmMethodInfersLetType(){ok(List.of("""
A:base.CaptureFree{ imm .foo: A -> base.Block#.let x= {this} .return {x} }
"""));}
@Test void typingContextShowsSupertypeWrittenByFullName(){fail("""
001| A:base.ToStr{ .str -> base.Void }
   |               --------^^^^^^^^^

While inspecting object literal instance of "base.Void" > method ".str" (line 1)
The body of method ".str" of type declaration "A" is an expression returning "base.Void".
Object literal is of type "base.Void" instead of a subtype of "base.Str".

Relevant code with inferred types:
A:base.ToStr{read .str:base.Str->base.Void}
""", List.of("""
A:base.ToStr{ .str -> base.Void }
"""));}
@Test void typingContextShowsSupertypeWrittenByUseAlias(){fail("""
002| A:Show{ .str -> base.Void }
   |         --------^^^^^^^^^

While inspecting object literal instance of "base.Void" > method ".str" (line 2)
The body of method ".str" of type declaration "A" is an expression returning "base.Void".
Object literal is of type "base.Void" instead of a subtype of "base.Str".

Relevant code with inferred types:
A:Show{read .str:base.Str->base.Void}
""", List.of("""
use base.ToStr as Show;
A:Show{ .str -> base.Void }
"""));}
@Test void useWithASimpleNameIsNotFullyQualified(){failWf("""
001| use Foo as Bar;
   |     ^^^

While inspecting package header
"use" directive refers to "Foo", which is not a full type name.
A "use" directive refers to a type of another package by its full type name, as in "use base.Str as Str;".
""", List.of("""
use Foo as Bar;
Foo:{}
A:{ .m(x: Bar): Foo -> x }
"""));}
@Test void sameCallInReadAndMutMethodsOfOneLiteral(){ok(List.of("""
Foo:{}
Id:{ #[T:*](t: T): T -> t }
K:{ read .a: read Foo; mut .b: read Foo }
User:{ .go(x: mut Foo): mut K -> mut K{ read .a -> Id#(x); mut .b -> Id#(x) } }
"""));}
@Test void deepWrittenOverrideOfAnInheritedSignature(){ok(List.of("""
N:{}
Top:{}
Box[X]:Top{}
B[X]:{ .m(x: Box[Box[X]]): N }
A:B[D]{ .m(x: Top): N -> N }
""".replace("D", box(97, "N"))));}
@Test void typeArgumentWithOpenCapabilityCapturedInANestedLiteral(){ok(List.of("""
Foo:{ .k: Foo -> this }
User:{ .m[X:*](x: imm X, f: base.F[X,Foo]): Foo; .go: Foo -> this.m(Foo, {y -> {#: Foo -> y.k}#}) }
"""));}
@Test void parameterUpdatedWithOpenCapabilityCapturedInANestedLiteral(){ok(List.of("""
A:{}
Foo[X]:{ .m(x: X): A }
Take:{ #[Z](f: Foo[Z]): A -> A }
Id:{ #[Y:*](y: Y, f: base.F[A]): imm Y -> base.Todo! }
Use:{ .go: A -> Take#{ .m(x) -> Id#(x, {# -> x}) } }
"""));}
@Test void capturedLambdaParameterInferredFromIsoArgument(){ok(List.of("""
A:{}
G[T:*]:{ .k(t: T): H }
H:{ .h: A }
Opt[T:*]:{ .match(m: G[T]): H }
Mk:{ #[T:*](t: T): Opt[T] -> base.Nope! }
U:{ .m(a: iso A): H -> Mk#(a).match{ .k(v1) -> { .h -> v1 } } }
"""));}
@Test void isoResultNormalizedToOpenCapabilityCapturedInANestedLiteral(){fail("""
002| U:{ .m: iso A -> base.Block#.let v1 = {A} .return {v1} }
   |     -------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".let(_,_)" > method ".m" (line 2)
The body of method ".m" of type declaration "U" is an expression returning "A".
Method call "mut base.Block[_].let(_,_)" has type "A" instead of a subtype of "iso A".

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
U:{.m:iso A->_#[imm,A].let[mut,A](mut base.ReturnStmt[A]{...},mut base.Continuation[_,_,_]{...})}
""", List.of("""
A:{}
U:{ .m: iso A -> base.Block#.let v1 = {A} .return {v1} }
"""));}
@Test void deepSignatureOfALiteralWithoutBodies(){ok(List.of("""
N:{}
Box[X]:{}
Foo[X]:{ mut .m(x: Box[Box[X]]): N }
Use:{ .go: Foo[D] -> Foo[D]{} }
""".replace("D", box(97, "N"))));}
@Test void deepSupertypeOfAnInferredLiteralWithoutBodies(){ok(List.of("""
N:{}
Box[X]:{}
C[X]:{}
Foo[X]:C[Box[Box[X]]]{}
Take:{ #(f: Foo[D]): N -> N }
Use:{ .go: N -> Take#{} }
""".replace("D", box(97, "N"))));}
@Test void callChainDeeperThanAThousand(){ok(List.of("""
N:{}
Box[X]:{ .wrap: Box[Box[X]] -> {} }
Ign:{ #[K](k: K): N -> N }
Use:{ .go(b: Box[N]): N -> Ign#(bW) }
""".replace("W", ".wrap".repeat(1000))));}
@Test void pickJoinsMutAndReadOfOneTypeParameter(){ok(List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
B[X:*]:{ .m(x:mut X, y:read X):read X -> Pick#(x,y) }
"""));}
@Test void pickOfATypeParameterAndVoid(){fail("""
002| C[X:*]:{ .m(x:X, y:base.Void):X -> Pick#(x,y) }
   |          --------------------------~~~~~~~~^~

While inspecting method ".m(_,_)" (line 2)
This call to method "Pick#(_,_)" cannot typecheck.
Argument 2 has type "base.Void".
That is not a subtype of "X" (the type required by the method signature).

Relevant code with inferred types:
Pick#[imm,X](x,y)
""", List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
C[X:*]:{ .m(x:X, y:base.Void):X -> Pick#(x,y) }
"""));}
@Test void pickOfThreeUnrelatedTypes(){fail("""
005| U:{ .m:A -> Pick3#(A,B,C) }
   |     --------~~~~~~~~~^~~~

While inspecting method ".m" (line 5)
This call to method "Pick3#(_,_,_)" cannot typecheck.
Argument 2 has type "B".
That is not a subtype of "A" (the type required by the method signature).

Relevant code with inferred types:
Pick3#[imm,A](A,B,C)
""", List.of("""
Pick3:{ #[T:*](a:T, b:T, c:T):T -> a }
A:{}
B:{}
C:{}
U:{ .m:A -> Pick3#(A,B,C) }
"""));}
@Test void readImmArgumentForAReadParameter(){ok(List.of("""
F2:{ #[T:*](x:read T):base.Void -> base.Void }
D[Y:*]:{ .m(y: read/imm Y): base.Void -> F2#(y) }
"""));}
@Test void literalForATypeParameterArgument(){failWf("""
002| H[X:*]:{ .m: X -> G#[X]({}) }
   |                         ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
G:{ #[T:*](x:T):T -> x }
H[X:*]:{ .m: X -> G#[X]({}) }
"""));}
@Test void literalArgumentForAReadImmParameter(){ok(List.of("""
F3:{ #[T:*](x: read/imm T):base.Void -> base.Void }
A:{}
U:{ .m:base.Void -> F3#(A{}) }
"""));}
@Test void baseIdReturningThis(){fail("""
001| I: base.BaseId[I,I]{ #(x)->this }
   |                            ^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.
""", List.of("""
I: base.BaseId[I,I]{ #(x)->this }
"""));}
@Test void baseIdCallingItself(){fail("""
001| I: base.BaseId[I,I]{ #(x)->this#(x) }
   |                            ^^^^^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Relevant code with inferred types:
this#(x)
""", List.of("""
I: base.BaseId[I,I]{ #(x)->this#(x) }
"""));}
@Test void pickJoinsIsoAndMutOfOneTypeParameter(){ok(List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
B[X:*]:{ .m(x:iso X, y:mut X):mut X -> Pick#(x,y) }
"""));}
@Test void pickJoinsMutAndIsoOfOneTypeParameter(){ok(List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
B[X:*]:{ .m(x:mut X, y:iso X):mut X -> Pick#(x,y) }
"""));}
@Test void returnOneTypeParameterAsAnother(){fail("""
001| A:{ .m[X:*,Y:*](x:mut X):mut Y -> x }
   |     ------------------------------^

While inspecting parameter "x" > method ".m(_)" (line 1)
The body of method ".m(_)" of type declaration "A" is an expression returning "mut X".
Parameter "x" has type "mut X" instead of a subtype of "mut Y".

Relevant code with inferred types:
A:{.m[X:*,Y:*](x:mut X):mut Y->x}
""", List.of("""
A:{ .m[X:*,Y:*](x:mut X):mut Y -> x }
"""));}
@Test void literalMethodParameterUnrelatedToTheTypeArgument(){fail("""
004| U:{ .m:Box[A] -> Box[A]{ .get(x:B):B -> x } }
   |     -------------~~~~~~~~^^^^^^^^^^^^^^^^~~

While inspecting object literal instance of "Box[A]" > method ".m" (line 4)
Invalid method signature for "Box[A].get(_)".
The method ".get(_)" accepts parameter 1 of type "B".
But "Box[_].get(_)" requires "A", which is not a subtype of "B".
The two types are unrelated.

Relevant code with inferred types:
Box[A]{.get(x:B):B->x}
""", List.of("""
A:{}
B:{}
Box[T:*]:{ .get(x:T):T }
U:{ .m:Box[A] -> Box[A]{ .get(x:B):B -> x } }
"""));}
@Test void baseIdInheritingHashFromANonBaseIdType(){failWf("""
001| I: base.BaseId[I,I], Impl{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "I"
Type declaration "I" implements "base.BaseId[_,_]".
It inherits the implementation of "#(_)" from "Impl", which does not implement "base.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "base.BaseId[_,_]".
""", List.of("""
I: base.BaseId[I,I], Impl{}
Impl:{ #(x:I):I -> x }
"""));}
@Test void baseIdAsOnANonContainer(){fail("""
002| I: base.BaseId[Box,Box]{ #(x)->x.as{ #(y)->y } }
   |                                ^^^^^^^^^^^^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Relevant code with inferred types:
x.as(base.BaseId[Box,Box]{#(y:Box):Box->y})
""", List.of("""
Box:{ .as(f: base.BaseId[Box,Box]):Box -> this }
I: base.BaseId[Box,Box]{ #(x)->x.as{ #(y)->y } }
"""));}
@Test void mutMethodInheritedPastAReadOverride(){ok(List.of("""
A:{ read .foo: base.Void -> base.Void; mut .foo: base.Void -> base.Void }
B:A{ read .foo: base.Void -> base.Void }
D:{ mut .foo: base.Void }
C:B,D{}
"""));}
@Test void lambdaMethodTypedByALaterMethod(){ok(List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
Two[X:*]:{ .a(x: X): base.Void; .b: X }
F:{ #[X:*](t: Two[X]): X -> t.b }
U:{ .m: base.Void -> Ig#(F#({ .a(x) -> base.Void; .b -> base.Void })) }
"""));}
@Test void lambdaMethodReturningThroughThisBeforeItsTypeIsKnown(){fail("""
004| U:{ .m: base.Void -> Ig#(F#({ .a -> this.b; .b -> base.Void })) }
   |                               ------~~~~^^

While inspecting method ".a" (line 4) > method ".m" (line 4)
This call to method ".b" cannot typecheck.
Method ".b" is not declared on type "U".
Parameter "this" has type "U".
Method ".b" is declared in the object literal instance of "Two[base.Void]", which has no self name.
A self name is declared with a single quote, as "'rect" in the example below:
  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect
    .area: Nat -> width * height;
    .str: Str -> "area: "+(rect.area.str);
    .withWidth(width': Nat): Rectangle -> this#(width', height);
  }}

Available methods on type "U":
- .m:base.Void

Relevant code with inferred types:
this.b
""", List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
Two[X:*]:{ .a: X; .b: X }
F:{ #[X:*](t: Two[X]): X -> t.b }
U:{ .m: base.Void -> Ig#(F#({ .a -> this.b; .b -> base.Void })) }
"""));}
@Test void literalReceiverWithAnUntypedParameter(){failWf("""
002| U:{ .m: A -> { .foo(x): A -> x }.foo(A) }
   |              --^^^^^^^^^^^^^^^--

While inspecting object literal instance of "A"
Missing parameter types for method ".foo(_)".
A method can omit types in its signature only when a supertype has a method ".foo(_)" to inherit the missing types from.
No supertype of object literal instance of "A" has a method ".foo(_)".
""", List.of("""
A:{}
U:{ .m: A -> { .foo(x): A -> x }.foo(A) }
"""));}
@Test void literalReceiverWithATypedParameter(){ok(List.of("""
A:{}
U:{ .m: A -> { .foo(x: A): A -> x }.foo(A) }
"""));}
@Test void baseIdCallingItselfOnItsArgument(){fail("""
001| I: base.BaseId[I,I]{ #(x)->x#(x) }
   |                            ^^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Relevant code with inferred types:
x#(x)
""", List.of("""
I: base.BaseId[I,I]{ #(x)->x#(x) }
"""));}
@Test void baseIdAsOnATypeParameterArgument(){fail("""
001| I[X:*]: base.BaseId[X,I[X]]{ #(x)->x.as[I[X]](this) }
   |                                    ^^^^^^^^^^^^^^^^

While inspecting the file
Type declaration "I[_]" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Relevant code with inferred types:
x.as[imm,I[X]](this)
""", List.of("""
I[X:*]: base.BaseId[X,I[X]]{ #(x)->x.as[I[X]](this) }
"""));}
@Test void readImmResultOfAMutTypeArgument(){ok(List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
A:{}
F:{ #[X:*](a: mut X): read/imm X -> base.Todo! }
U:{ .m(x: mut A): base.Void -> Ig#(F#(x)) }
"""));}
@Test void subtypeArgumentWithAnUninferredTypeArgument(){ok(List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
Box[X:*]:{ .get: X }
SubBox[X:*]:Box[X]{}
Mk:{ #[Y:*]: SubBox[Y] -> base.Todo! }
F:{ #[X:*](b: Box[X], x: X): X -> x }
U:{ .m: base.Void -> Ig#(F#(Mk#, base.Void)) }
"""));}
@Test void literalWithAMethodForAnExplicitTypeParameterArgument(){fail("""
003| H[X:*]:{ .m: X -> G#[X](A{ .k -> base.Void }) }
   |          ---------------^^^^^^^^^^^^^^^^^^^^-

While inspecting object literal instance of "A" > method ".m" (line 3)
Object literal instance of "A" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.

Relevant code with inferred types:
A{.k:base.Void->base.Void}
""", List.of("""
G:{ #[T:*](x: T): T -> x }
A:{ .k: base.Void }
H[X:*]:{ .m: X -> G#[X](A{ .k -> base.Void }) }
"""));}
@Test void literalForAnExplicitTypeParameterArgument(){fail("""
003| H[X:*]:{ .m: X -> G#[X](A{}) }
   |          ---------------^^^-

While inspecting object literal instance of "A" > method ".m" (line 3)
Object literal instance of "A" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
G:{ #[T:*](x: T): T -> x }
A:{}
H[X:*]:{ .m: X -> G#[X](A{}) }
"""));}
@Test void literalReceiverExpectedAsTheEnclosingLiteralType(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, { .j: A -> s }.j) } }
"""));}
@Test void literalImplementingTheEnclosingLiteralType(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, { .k -> s; .v -> base.Void }) } }
"""));}
@Test void anonymousLiteralImplementingTheEnclosingAnonymousLiteralType(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> {'s .k -> s; .v -> G#(s, { .k -> s; .v -> base.Void }) } }
"""));}
@Test void literalExpectedAsTheTypeOfTheSelfName(){fail("""
003| U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
   |     -----------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "A" > method ".v" (line 3) > method ".m" (line 3)
This object literal is missing a required method.
Missing: "imm .k".
Required by: "A".
Add an implementation for ".k" inside the object literal.
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void literalExpectedAsTheTypeOfTheSelfNameWithAnIndirectSupertype(){fail("""
004| U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
   |     -----------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "A" > method ".v" (line 4) > method ".m" (line 4)
This object literal is missing a required method.
Missing: "imm .k".
Required by: "A".
Add an implementation for ".k" inside the object literal.
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A0:{}
A:A0{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void literalExpectedAsTheTypeOfAnAnonymousSelfName(){failWf("""
002| U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, {}) }.j }
   |                                                 ^^

While inspecting object literal "{...}" (line 2)
Type inference concluded that the object literal at line 2, column 49 should implement the object literal at line 2, column 22.
An object literal can only implement a standalone type.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, {}) }.j }
"""));}
@Test void literalWithAMethodExpectedAsTheTypeOfAnAnonymousSelfName(){failWf("""
002| U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, { .j -> base.Void }) }.j }
   |                                                 ^^^^^^^^^^^^^^^^^^^

While inspecting object literal "{...}" (line 2)
Type inference concluded that the object literal at line 2, column 49 should implement the object literal at line 2, column 22.
An object literal can only implement a standalone type.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, { .j -> base.Void }) }.j }
"""));}
@Test void anonymousSelfNameAsBothArguments(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, s) }.j }
"""));}
@Test void literalExpectedAsATypeDeclaredInAMethod(){fail("""
003| U:{ .m: A -> Foo:A{'s .k -> s; .v -> G#(s, {}) } }
   |     ---------------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "Foo" > method ".v" (line 3) > method ".m" (line 3)
The type "Foo" is not standalone: it is declared inside a method body.
Only a standalone type can be implemented or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> Foo:A{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void literalExpectedAsACaptureFreeTypeDeclaredInAMethod(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> Foo:A,base.CaptureFree{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void typeArgumentFromAnAnonymousSelfNameAndAnotherType(){failWf("""
003| U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, B) }.j }
   |                                           ^^^^^^^^

While inspecting method call "#(_,_)"
The generic type argument "X" of "#" is inferred from the arguments, but they disagree: some need the anonymous type of the object literal at line 3, column 22, some need "B".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "G#[Type1](s, B)".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
B:{}
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, B) }.j }
"""));}
@Test void literalReturningTheSelfNameBeforeAnArgument(){ok(List.of("""
Box[E:*]:{ .get: E }
H:{ #[X:*](b: Box[X], x: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> H#({ .get -> s }, s.k) } }
"""));}
@Test void literalReturningTheSelfNameAfterAnArgument(){ok(List.of("""
Box[E:*]:{ .get: E }
H:{ #[X:*](x: X, b: Box[X]): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> H#(s.k, { .get -> s }) } }
"""));}
@Test void literalReturningAnAnonymousSelfName(){fail("""
004| U:{ .m: base.Void -> {'s .j: base.Void -> H#({ .get -> s }, B) }.j }
   |                          -----------------~~~~~~~~~~~~~~~~~~^~

While inspecting method ".j" (line 4) > method ".m" (line 4)
This call to method "H#(_,_)" cannot typecheck.
Argument 2 has type "B".
That is not a subtype of the anonymous type of the object literal at line 4, column 22 (the type required by the method signature).

Name "_BU" stands for the anonymous type of the object literal at line 4, column 22.

Relevant code with inferred types:
H#[imm,_BU](Box[_BU]{.get:_BU->s},B)
""", List.of("""
Box[E:*]:{ .get: E }
H:{ #[X:*](b: Box[X], x: X): base.Void -> base.Void }
B:{}
U:{ .m: base.Void -> {'s .j: base.Void -> H#({ .get -> s }, B) }.j }
"""));}
@Test void methodTArgsArityError_emptyBrackets(){fail("""
003| User:{ read .m(i:Id,a:mut A):mut A-> i.id[](a); }
   |        ------------------------------~^^^~~~~~

While inspecting method ".m(_,_)" (line 3)
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
Method ".id(_)" declares 1 generic type parameter.
Declared generic type parameters: "X".
This call provides no generic type arguments.

Relevant code with inferred types:
i.id[read](a)
""", List.of("""
A:{}
Id:{ read .id[X:imm,mut,read](x:X):X->x; }
User:{ read .m(i:Id,a:mut A):mut A-> i.id[](a); }
"""));}
@Test void methodTArgsArityError_capabilityOnlyBrackets(){fail("""
004| User:{ .go(x: Foo): mut K -> { read .a -> Id#[imm](x); .b -> Id#[imm](x) } }
   |                                -----------~~^~~~~~~~~

While inspecting method ".a" (line 4) > method ".go(_)" (line 4)
This call to method "Id#(_)" cannot typecheck.
Wrong number of generic type arguments for "#(_)".
Method "#(_)" declares 1 generic type parameter.
Declared generic type parameters: "T".
This call provides no generic type arguments.

Relevant code with inferred types:
Id#(x)
""", List.of("""
Foo:{}
Id:{ #[T:*](t: T): T -> t }
K:{ read .a: Foo; mut .b: read Foo }
User:{ .go(x: Foo): mut K -> { read .a -> Id#[imm](x); .b -> Id#[imm](x) } }
"""));}
@Test void methodTArgsArityError_onlyACapability(){fail("""
003| User:{ read .m(i:Id,a:mut A):mut A-> i.id[read](a); }
   |        ------------------------------~^^^~~~~~~~~~

While inspecting method ".m(_,_)" (line 3)
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
Method ".id(_)" declares 1 generic type parameter.
Declared generic type parameters: "X".
This call provides no generic type arguments.

Relevant code with inferred types:
i.id[read](a)
""", List.of("""
A:{}
Id:{ read .id[X:imm,mut,read](x:X):X->x; }
User:{ read .m(i:Id,a:mut A):mut A-> i.id[read](a); }
"""));}
@Test void methodTArgsInferredWithoutBrackets(){ok(List.of("""
A:{}
Id:{ read .id[X:imm,mut,read](x:X):X->x; }
User:{ read .m(i:Id,a:mut A):mut A-> i.id(a); }
"""));}
@Test void matchResultInferredFromAllTheCases(){ok(List.of("""
use base.MF as MF;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
North: Direction {::.north}
East : Direction {::.east}
South: Direction {::.south}
West : Direction {::.west}
DirectionMatch[R:**]: { mut .north: R; mut .east: R; mut .south: R; mut .west: R; }
Direction: {
  read .match[R: **](m: mut DirectionMatch[R]): R;
  .turn2: Direction -> Blocks#
    .let d= {this.match{ .north -> East; .east -> South; .south -> West; .west -> North; }}
    .return{d};
  }
"""));}
@Test void declaredReceiverLiteralKeepsItsCapability(){ok(List.of("""
A:{ .k: A -> mut Foo:{ mut .bar: A -> A }.bar }
"""));}
@Test void declaredReceiverLiteralCapturesAMutParameter(){ok(List.of("""
Bar:{ mut .b: base.Void }
A:{ .k(x: mut Bar): base.Void -> mut Foo:{ mut .z: base.Void -> x.b }.z }
"""));}
@Test void declaredReceiverLiteralSelfNameIsNotImm(){fail("""
002| A:{ .k: base.Void -> read Foo:{'s read .z: base.Void -> Use#s }.z }
   |                                   ----------------------~~~~^

While inspecting method ".z" (line 2) > method ".k" (line 2)
This call to method "Use#(_)" cannot typecheck.
Argument 1 has type "read Foo".
Parameter "s" has type "read Foo" instead of a subtype of "imm Foo".

Type required by each promotion:
- "imm Foo" (As declared, Strengthen result)

Relevant code with inferred types:
A:{.k:base.Void->read Foo:{'s read .z:base.Void->Use#(s)}.z[read]}
""", List.of("""
Use:{ #(f: Foo): base.Void -> base.Void }
A:{ .k: base.Void -> read Foo:{'s read .z: base.Void -> Use#s }.z }
"""));}
@Test void joinOfTypesImplementingAGenericHeadTwice(){ok(List.of("""
Box[T]:{}
C:Box[A],Box[C]{}
D:Box[A]{}
A:{ .m[X](x: X, y: X): X -> y; .k: Box[A] -> this.m(C, D) }
"""));}
@Test void joinOfTypesImplementingAGenericHeadTwiceIsAmbiguous(){failWf("""
004| A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
   |                                                                          ^^^^^^^^^^^^

While inspecting method call ".m(_,_)"
The generic type argument "X" of ".m" is inferred from the arguments, but they disagree: some need "C", some need "D".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.m[Type1](C, D)".
""", List.of("""
Box[T]:{}
C:Box[A],Box[C]{}
D:Box[A]{}
A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
"""));}
@Test void joinOfTypesImplementingAGenericHeadTwiceInTheOtherOrderIsAmbiguous(){failWf("""
004| A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
   |                                                                          ^^^^^^^^^^^^

While inspecting method call ".m(_,_)"
The generic type argument "X" of ".m" is inferred from the arguments, but they disagree: some need "C", some need "D".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.m[Type1](C, D)".
""", List.of("""
Box[T]:{}
C:Box[C],Box[A]{}
D:Box[A]{}
A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
"""));}
@Test void argumentImplementingAGenericHeadTwiceIsAmbiguous(){fail("""
003| A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
   |                                  ---------~~~~~~~^~

While inspecting method ".k" (line 3)
This call to method "A.m(_)" cannot typecheck.
Argument 1 has type "C".
That is not a subtype of "Box[base.Void]" (the type required by the method signature).

Relevant code with inferred types:
this.m[imm,base.Void](C)
""", List.of("""
Box[T]:{}
C:Box[A],Box[C]{}
A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
"""));}
@Test void argumentImplementingAGenericHeadTwiceInTheOtherOrderIsAmbiguous(){fail("""
003| A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
   |                                  ---------~~~~~~~^~

While inspecting method ".k" (line 3)
This call to method "A.m(_)" cannot typecheck.
Argument 1 has type "C".
That is not a subtype of "Box[base.Void]" (the type required by the method signature).

Relevant code with inferred types:
this.m[imm,base.Void](C)
""", List.of("""
Box[T]:{}
C:Box[C],Box[A]{}
A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
"""));}
@Test void joinOfASubtypeRefiningAGenericHeadOfItsSupertype(){ok(List.of("""
Box[T]:{}
R:Box[R]{}
S:R,Box[S]{}
A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(R, S)) }
"""));}
@Test void nestedLiteralCapturesALateInferredParameter(){ok(List.of("""
use base.F as F;
Foo:{ .foo: A }
A:{
  .app[T](t: T, f: F[T,A]): A -> f#t;
  .ig(z: Foo): A -> z.foo;
  .ig2[W](w: W): A -> A;
  .k[X](x: X): A -> this.app(x, {y -> this.ig({ .foo -> this.ig2(y) })});
  }
"""));}
@Test void nestedLiteralWithAGenericCapturesALateInferredParameter(){ok(List.of("""
use base.F as F;
Foo:{ .foo: A }
A:{
  .app[T](t: T, f: F[T,A]): A -> f#t;
  .ig(z: Foo): A -> z.foo;
  .ig2[W](w: W): A -> A;
  .ig3(a: A): A -> a;
  .k[X,Y](x: X, v: Y): A -> this.app(x, {y -> this.ig({ .foo -> this.ig2(v).ig3(this.ig2(y)) })});
  }
"""));}
@Test void writtenLiteralArgumentDecidesATypeArgument(){ok(List.of("""
Sup:{}
Sub:Sup{}
Box[X]:{}
K:{ #[X](a: X, b: Box[X]): X -> a }
M:{ .m(y: Sub): Sup -> K#(y, Box[Sup]) }
"""));}
@Test void writtenEmptyLiteralArgumentDecidesATypeArgument(){ok(List.of("""
Sup:{}
Sub:Sup{}
Box[X]:{}
K:{ #[X](a: X, b: Box[X]): X -> a }
M:{ .m(y: Sub): Sup -> K#(y, Box[Sup]{}) }
"""));}
@Test void emptyLiteralArgumentDoesNotDecideATypeArgument(){ok(List.of("""
Sup:{}
Sub:Sup{}
Box[X,Y]:{}
K:{ #[X,Y](a: X, b: Box[X,Y], c: Y): X -> a }
M:{ .m(y: Sub, z: Sup): Sup -> K#(y, {}, z) }
"""));}
@Test void emptyLiteralArgumentFollowsATypeArgumentBelowTheResultType(){ok(List.of("""
Sup:{}
Sub:Sup{}
Box[X]:{}
K:{ #[X](a: X, b: Box[X]): X -> a }
M:{ .m(y: Sub): Sup -> K#(y, {}) }
"""));}
@Test void innerLiteralCapturesALateInferredParameter(){ok(List.of("""
use base.F as F;
Foo:{ .foo: A }
Ret[R]:{ #: R }
A:{
  .app[T](t: T, f: F[T,A]): A -> f#t;
  .ig(z: Foo): A -> z.foo;
  .ig4[W](r: Ret[W]): A -> A;
  .k[X](x: X): A -> this.app(x, {y -> this.ig({ .foo -> this.ig4({y}) })});
  }
"""));}
@Test void typeExpressionDoesNotShiftFreshGenericNames(){ok(List.of("""
S:{ .s[K](k: K): K -> k; }
D[K]:S{}
T[K]:D[K]{ .m: S -> S.s[S]{.s k -> k}; }
"""));}
@Test void selfNameCallWithAnExpectedTypeGetsItsCapability(){ok(List.of("""
A:{ mut .a: mut A }
B:{ #: mut A -> mut A{'s .a -> s.a} }
"""));}
@Test void letOfAGenericParameterUsedInTheReturn(){ok(List.of("""
A:{ .k[X](x: X): base.Void -> base.Block#.let y= {x} .return{ base.Block#(y, base.Void) } }
"""));}
@Test void selfNameCallOnAnImmLiteralGetsItsCapability(){ok(List.of("""
A:{}
Foo:{ .foo: A; read .r: A }
B:{ .k: A -> B.ig(Foo{'s .foo -> s.r; read .r -> A }); .ig(z: Foo): A -> z.foo }
"""));}
@Test void declaredReceiverLiteralCapturesThisInAReadMethod(){ok(List.of("""
A:{ read .q: A; read .k: A -> read Foo:{ read .z: A -> this.q }.z }
"""));}
@Test void emptyLiteralWithAnExpectedTypeWidenedToASupertype(){ok(List.of("""
C:base.WidenTo[C]{}
B:C{}
A:{ .m: B -> {} }
"""));}
@Test void emptyLiteralArgumentWithAnExpectedNumberLiteralType(){ok(List.of("""
A:{ .m(x: 45): A -> A; .k: A -> this.m({}) }
"""));}
@Test void typeNameExpressionWidenedToASupertypeWithALessSpecificMethod(){ok(List.of("""
C:{ .k: C }
B:C,base.WidenTo[C]{ .k: B -> this }
A:{ .m: C -> B }
"""));}
@Test void typeNameExpressionWidenedPastAnIntermediateOverride(){ok(List.of("""
C:{ .k: C -> this }
D:C{ .k: D -> this }
B:D,base.WidenTo[C]{}
A:{ .m: C -> B }
"""));}
@Test void typeNameExpressionWidenedToAnUnrelatedTypeWithAnotherGenericArity(){ok(List.of("""
C:{ .k[Y](y: Y): Y -> y }
B:base.WidenTo[C]{ .k(x: C): B -> this }
A:{ .m: B -> B }
"""));}
@Test void emptyLiteralWithAnExpectedTypeWidenedToAnUnrelatedAbstractType(){ok(List.of("""
C:{ .k: C }
B:base.WidenTo[C]{}
A:{ .m: B -> {} }
"""));}
@Test void emptyLiteralRefinedFromAReadExpectedTypeToAnImmExpectedType(){ok(List.of("""
P:{}
Box[X:**]:{ .get: X }
Ids:{ #[X:**](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[P]): read P -> Ids#({}, b) }
"""));}
@Test void emptyLiteralRefinedFromAnIsoExpectedTypeToAMutExpectedType(){ok(List.of("""
P:{}
Box[X:**]:{ .get: X }
Ids:{ #[X:**](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[mut P]): iso P -> Ids#({}, b) }
"""));}
@Test void emptyLiteralWithAMutAbstractMethodRefinedToAnImmExpectedType(){ok(List.of("""
P:{ mut .k: P }
Box[X:**]:{ .get: X }
Ids:{ #[X:**](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[P]): read P -> Ids#({}, b) }
"""));}
@Test void emptyLiteralRefinedFromAnAbstractSupertypeToAConcreteSubtype(){ok(List.of("""
P:{}
Sup:{ .name: P }
Con:Sup{ .name -> P }
Box[X]:{ .get: X }
Ids:{ #[X](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[Con]): Sup -> Ids#({}, b) }
"""));}
@Test void emptyLiteralRefinedFromASupertypeToASubtypeWithOneMoreMethod(){ok(List.of("""
Sup:{}
Sub:Sup{ .k: Sub -> this }
Box[X]:{ .get: X }
Ids:{ #[X](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[Sub]): Sup -> Ids#({}, b) }
"""));}
@Test void typeExpressionOfATypeWithAnOperatorMethodContainingAnArrow(){ok(List.of("""
Q:{ -->(a: Q): Q -> a }
A:{ .k: Q -> Q }
"""));}
@Test void typeExpressionOfATypeWithAClosedCurlyStringLiteralTypeInAMethod(){ok(List.of("""
Q:{ .m: "}" -> "}" }
A:{ .k: Q -> Q }
"""));}
@Test void lambdaParameterCapturedInAMutLiteralAndUsedAsMutHIsMut(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mutH A): A -> a.m }
G:{ mut #: A }
F1[X:*,R:*]:{ #(x: X): R }
Ap:{ #[X:*,R:*](f: F1[X,R]): R -> this#f }
User:{ .use: mut G -> Ap#{x -> mut G{ Mut#x }} }
"""));}
@Test void lambdaParameterCapturedInAMutLiteralAndUsedAsMutHIsMutAlsoWhenTheBoundAllowsMutH(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mutH A): A -> a.m }
G:{ mut #: A }
F1[X:**,R:*]:{ #(x: X): R }
Ap:{ #[X:**,R:*](f: F1[X,R]): R -> this#f }
User:{ .use: mut G -> Ap#{x -> mut G{ Mut#x }} }
"""));}
@Test void lambdaParameterCapturedInAReadLiteralAndUsedAsReadHIsRead(){ok(List.of("""
A:{ read .m: A -> A }
Use:{ #(a: readH A): A -> a.m }
G:{ read #: A }
F1[X:**,R:**]:{ #(x: X): R }
Ap:{ #[X:**,R:**](f: F1[X,R]): R -> this#f }
User:{ .use: read G -> Ap#{x -> read G{ Use#x }} }
"""));}
@Test void receiverTypeArgumentAndADifferentTypeArgumentOfAnArgumentIsATypeError(){fail("""
004| User:{ .m(x: Box[A], y: Box[B]): Box[A] -> x.put(y) }
   |        ------------------------------------~~~~~~^~

While inspecting method ".m(_,_)" (line 4)
This call to method "Box[_].put(_)" cannot typecheck.
Argument 1 has type "Box[B]".
That is not a subtype of "Box[A]" (the type required by the method signature).

Relevant code with inferred types:
x.put(y)
""", List.of("""
A:{}
B:A{}
Box[T]:{ .put(b: Box[T]): Box[T] -> this }
User:{ .m(x: Box[A], y: Box[B]): Box[A] -> x.put(y) }
"""));}
@Test void emptyLiteralArgumentNextToATypedArgumentGivesNoConstraint(){ok(List.of("""
Sup:{ .k: Sup }
Closed[T]:Sup{ read .close: read T }
A:Closed[A]{ .close->this; .k->this }
Ids:{ #[X](a: X, b: X): X -> a }
User:{ .m(c: Closed[A]): Sup -> Ids#({}, c) }
"""));}
@Test void argumentOfACallOnAReceiverOfUnknownTypeDecidesTheTypeOfTheReceiver(){ok(List.of("""
A:{ .foo(a: A): A -> a }
Id:{ #(a: A): A -> a }
F[T,R]:{ #(t: T): R }
Use:{ #[T,R](f: F[T,R]): Use -> this }
User:{ .m: Use -> Use#{x -> x.foo(Id#x)} }
"""));}
@Test void siblingsWithAChainOfCommonSupertypesInferTheLowest(){ok(List.of("""
Living:{}
Animal:Living{ .me: Animal -> this }
Cat:Animal{}
Dog:Animal{}
Ids:{ #[X](a: X, b: X): X -> a }
User:{ .m(c: Cat, d: Dog): Animal -> Ids#(c, d).me }
"""));}
@Test void typeGrowsForeverInsideAnArgument(){failWf("""
007| Use:{ .go: N -> Take#{ .m(x) -> Pair#(x, Wrap#(x)) } }
   |                                          ^^^^^^^^

While inspecting method call "#(_)"
Type inference finds no type for method call "#(_)".
Each round of inference nests its type one level deeper, as "Box[Box[Box[...]]]"; it would grow without bound.
""", List.of("""
N:{}
Box[X]:{}
Wrap:{ #[Y](y: Y): Box[Y] -> {} }
Pair:{ #[T](a: T, b: T): N -> N }
Foo[X]:{ .m(x: X): N }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go: N -> Take#{ .m(x) -> Pair#(x, Wrap#(x)) } }
"""));}
@Test void selfNameCallInALiteralOfUnknownCapabilityDoesNotDecideATypeArgument(){failWf("""
004| User:{ .go: A -> Take#{'s .mk -> A; .get -> s.mk }.mk }
   |                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Foo[_]"
Type inference concluded that this object literal implements "Foo[?]",
but it could not infer generic type argument 1 for generic type parameter "T" of "Foo[_]".
Write the generic type argument explicitly, as in "Foo[Type1]{...}".
""", List.of("""
A:{}
Foo[T]:{ .mk: A; .get: T }
Take:{ #[T](f: Foo[T]): Foo[T] -> f }
User:{ .go: A -> Take#{'s .mk -> A; .get -> s.mk }.mk }
"""));}
@Test void aParameterBesideADestructuringPatternIsPrintedWithANote(){fail("""
002| User:{ .u({.a,.b}: Pt, x: base.Str): base.Str -> a }
   |        ------------------------------------------^

While inspecting parameter "a" > method "#(_,_,_)" (line 2) > method ".u(_,_)" (line 2)
Method "#(_,_,_)" inside the object literal instance of "mut base.MF[base.Nat,base.Nat,base.Str,base.Str]" (line 2)
is implemented with an expression returning "base.Nat".
Parameter "a" has type "base.Nat" instead of a subtype of "base.Str".

Name "_ax" is parameter "x", renamed by the desugaring of a nominal pattern in the same method.

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
User:{.u(Pt,x:base.Str):base.Str->base.Destruct#[imm,base.Nat,base.Nat,base.Str,base.Str](_.a,_.b,_ax,mut base.MF[base.Nat,base.Nat,base.Str,base.Str]{mut #(a:base.Nat,b:base.Nat,x:base.Str):base.Str->a})}
""", List.of("""
Pt:{ .a: base.Nat; .b: base.Nat }
User:{ .u({.a,.b}: Pt, x: base.Str): base.Str -> a }
"""));}
@Test void aRenamedGenericTypeParameterAsACandidateIsPrintedWithANote(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the return type of method "imm .get" with 0 parameters.
Candidates: "_AX", "Sup1".
The candidates are different types and "_AX" is a generic type parameter, so no method ".get" can implement all the candidates.

Name "_AX" stands for generic type parameter "X" of an inherited method, renamed because "X" already names a type or another generic type parameter.
""", List.of("""
Sup1:{ .get[X]:X }
Sup2:{ .get[X]:Sup1 }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void aDestructuringParameterIsPrintedWithANote(){fail("""
002| U:{ .u({.a}: P): U -> a }
   |     ------------------^

While inspecting parameter "a" > method "#(_)" (line 2) > method ".u(_)" (line 2)
Method "#(_)" inside the object literal instance of "mut base.MF[P,U]" (line 2)
is implemented with an expression returning "P".
Parameter "a" has type "P" instead of a subtype of "U".

Name "_adiv" is a parameter added by the desugaring of a nominal pattern: for a parameter "{.a, .b}: P", "_adiv" is that parameter, and "a" and "b" stand for "_adiv.a" and "_adiv.b".

Relevant code with inferred types:
U:{.u(P):U->base.Destruct#[imm,P,U](_adiv.a,mut base.MF[P,U]{mut #(a:P):U->a})}
""", List.of("""
P:{ .a: P }
U:{ .u({.a}: P): U -> a }
"""));}
@Test void aFreshNameStandingForTwoNamesGetsNoNote(){fail("""
003| B:{ .u({.a}: P, xyzwb: P): A -> xyzwb }
   |     ----------------------------^^^^^

While inspecting parameter "xyzwb" > method "#(_,_)" (line 3) > method ".u(_,_)" (line 3)
Method "#(_,_)" inside the object literal instance of "mut base.MF[P,P,A]" (line 3)
is implemented with an expression returning "P".
Parameter "xyzwb" has type "P" instead of a subtype of "A".

Name "_adiv" is a parameter added by the desugaring of a nominal pattern: for a parameter "{.a, .b}: P", "_adiv" is that parameter, and "a" and "b" stand for "_adiv.a" and "_adiv.b".

Relevant code with inferred types:
B:{.u(P,xyzwb:P):A->base.Destruct#[imm,P,P,A](_adiv.a,_axyzw,mut base.MF[P,P,A]{mut #(a:P,xyzwb:P):A->xyzwb})}
""", List.of("""
P:{ .a: P }
A:{ .u({.a}: P, xyzwa: P): P -> a }
B:{ .u({.a}: P, xyzwb: P): A -> xyzwb }
"""));}
@Test void aCompressedMethodKeepsItsNameAndParameterNames(){fail("""
004| U:{ .m(a:Apple1234567890): Use -> Use#(mut F{ .a(x, y) -> x; mut .b(x) -> x; .c -> a }, this) }
   |     ------------------------------~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^^^^~

While inspecting method ".m(_)" (line 4)
This call to method "Use#(_,_)" cannot typecheck.
Argument 2 has type "U".
That is not a subtype of "Apple1234567890" (the type required by the method signature).

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
Use#(mut F{.a(x,y)->x;mut .b(x:Apple1234567890):Apple1234567890->x;.c:Apple1234567890->a},this)
""", List.of("""
Apple1234567890:{}
F:{ .a(x:Apple1234567890, y:Apple1234567890): Apple1234567890; mut .b(x:Apple1234567890): Apple1234567890; .c: Apple1234567890 }
Use:{ #(f:mut F, a:Apple1234567890): Use -> this }
U:{ .m(a:Apple1234567890): Use -> Use#(mut F{ .a(x, y) -> x; mut .b(x) -> x; .c -> a }, this) }
"""));}
@Test void aCompressedCallPrintsAHoleForItsReceiverAndArguments(){fail("""
003| U:{ .m(appleAppleApple1234567890:Apple1234567890): Use -> Use#(appleAppleApple1234567890 + appleAppleApple1234567890, appleAppleApple1234567890 + appleAppleApple1234567890, appleAppleApple1234567890 + appleAppleApple1234567890, this) }
   |     ------------------------------------------------------~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^^^^~

While inspecting method ".m(_)" (line 3)
This call to method "Use#(_,_,_,_)" cannot typecheck.
Argument 4 has type "U".
That is not a subtype of "Apple1234567890" (the type required by the method signature).

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
Use#(_ + _,_ + _,appleAppleApple1234567890 + appleAppleApple1234567890,this)
""", List.of("""
Apple1234567890:{ +(x:Apple1234567890): Apple1234567890 -> this }
Use:{ #(a:Apple1234567890, b:Apple1234567890, c:Apple1234567890, u:Apple1234567890): Use -> this }
U:{ .m(appleAppleApple1234567890:Apple1234567890): Use -> Use#(appleAppleApple1234567890 + appleAppleApple1234567890, appleAppleApple1234567890 + appleAppleApple1234567890, appleAppleApple1234567890 + appleAppleApple1234567890, this) }
"""));}
@Test void anOperatorCallIsPrintedInfixAndGroupedWhenItIsAReceiver(){fail("""
003| U:{ .m(a:N, b:N): W -> a + b.get }
   |     -------------------^^^^^^^^^

While inspecting method call ".get" > method ".m(_,_)" (line 3)
The body of method ".m(_,_)" of type declaration "U" is an expression returning "N".
Method call "N.get" has type "N" instead of a subtype of "W".

Relevant code with inferred types:
U:{.m(a:N,b:N):W->(a + b).get}
""", List.of("""
N:{ +(n:N): N -> this; .get: N -> this }
W:{}
U:{ .m(a:N, b:N): W -> a + b.get }
"""));}
@Test void aCompressedMethodTakingTheImplicitParameterIsPrintedWithoutParameters(){fail("""
005| User:{ .u(a:A): A -> Use#({::.fooooooooooooooooooooooooooooooooooooooo}, G{ .m -> ::.fooooooooooooooooooooooooooooooooooooooo; .k -> A }, this) }
   |        --------------~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^^^^~

While inspecting method ".u(_)" (line 5)
This call to method "Use#(_,_,_)" cannot typecheck.
Argument 3 has type "User".
That is not a subtype of "A" (the type required by the method signature).

Relevant code with inferred types, where "_", "{...}" and method signatures without types mark omitted code:
Use#(F{#->::.fooooooooooooooooooooooooooooooooooooooo},G{.m->::.fooooooooooooooooooooooooooooooooooooooo;.k:A->A},this)
""", List.of("""
A:{ .fooooooooooooooooooooooooooooooooooooooo: A -> this }
F:{ #(a:A): A }
G:{ .m(a:A): A; .k: A }
Use:{ #(f:F, g:G, b:A): A -> b }
User:{ .u(a:A): A -> Use#({::.fooooooooooooooooooooooooooooooooooooooo}, G{ .m -> ::.fooooooooooooooooooooooooooooooooooooooo; .k -> A }, this) }
"""));}
@Test void aLongLiteralIsPrintedInFull(){fail("""
001| B:{ .m: B -> "a string literal longer than fifteen" }
   |     ---------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.Str" > method ".m" (line 1)
The body of method ".m" of type declaration "B" is an expression returning "base.Str".
Object literal is of type "base.Str" instead of a subtype of "B".

Relevant code with inferred types:
B:{.m:B->"a string literal longer than fifteen"}
""", List.of("""
B:{ .m: B -> "a string literal longer than fifteen" }
"""));}
}
