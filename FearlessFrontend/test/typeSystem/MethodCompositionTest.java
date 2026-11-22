package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public final class MethodCompositionTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failWf(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input);
  }

@Test void noMeths(){ok(List.of("""
A:{}
"""));}
@Test void oneMeth(){ok(List.of("""
A:{ .foo(a:A):A->this }
"""));}
@Test void twoMethOneAbs(){ok(List.of("""
A:{ .foo(a:A):A->this; .bar(a1: A, a2: read A): mut A }
"""));}
@Test void twoMethBothImpl(){ok(List.of("""
A:{ .foo(a:A):A->this; .bar(a1: A, a2: read A): mut A->{} }
"""));}
@Test void oneAbs(){ok(List.of("""
A:{ .foo(a:A):A }
"""));}
@Test void noOverride(){ok(List.of("""
A:{ .foo(a:A):A }
B:A{ .bar(b:B):B }
"""));}
@Test void sameMeth(){ok(List.of("""
A:{ .foo(a:A):A }
B:A{ .foo(b:A):A }
"""));}
@Test void refineRt(){ok(List.of("""
A:{ .foo(a:A):A }
B:A{ .foo(b:A):B }
"""));}
@Test void refineRtAndStrengthenParam(){fail("""
003| B:A{ .foo(b:B):Int }
   | -----^^^^^^^^^^^^^--

While inspecting type declaration "B"
Invalid method signature for "B.foo(_)".
The method ".foo(_)" accepts parameter 1 of type "B".
But "A.foo(_)" requires "A", which is not a subtype of "B".
It is instead a supertype: you are strengthening the parameter instead of weakening it.
""", List.of("""
Str:{} Int:{}
A:{ .foo(a:A):Str }
B:A{ .foo(b:B):Int }
"""));}
@Test void ownMethodStrengthensParamOfBothSupers(){fail("""
001| A:B,C{ .foo(a:A):A }
   | -------^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.foo(_)".
The method ".foo(_)" accepts parameter 1 of type "A".
But "B.foo(_)" requires "B", which is not a subtype of "A".
It is instead a supertype: you are strengthening the parameter instead of weakening it.
""", List.of("""
A:B,C{ .foo(a:A):A }
B:{ .foo(b:B):B }
C:{ .foo(c:C):C }
"""));}
@Test void refineRtOnly(){ok(List.of("""
A:B{ .m: A }
B:{ .m: B }
"""));}
@Test void sameRt(){ok(List.of("""
Int:{}
A:B{ .m: Int }
B:{ .m: Int }
"""));}
@Test void unrelatedRt(){fail("""
002| A:B{ .m: Str }
   | -----^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Str".
But "B.m" returns type "Int", which is not a supertype of "Str".
The two types are unrelated.
""", List.of("""
Int:{} Str:{}
A:B{ .m: Str }
B:{ .m: Int }
"""));}
@Test void twoSupersPickedByOwnMeth(){ok(List.of("""
A:B,C{ .m: A }
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void twoSupersDisagreeOnRt(){failWf("""
001| A:B,C{}
   | ^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the signature of method "imm .m".
Signatures as inherited by type declaration "A":
-       B.m: B
-       C.m: C
"A" must declare method ".m".
"A.m" return type must be a subtype of "B" and "C".
Such type currently visible: "A".
""", List.of("""
A:B,C{}
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void twoSupersDisagreeOnRtInherited(){failWf("""
003| AA:B,C{}
   | ^^^^^^^^

While inspecting type declaration "AA"
Supertypes disagree on the signature of method "imm .m".
Signatures as inherited by type declaration "AA":
-       B.m: B
-       C.m: C
"AA" must declare method ".m".
"AA.m" return type must be a subtype of "B" and "C".
Such types currently visible:
- "A"
- "AA"
""", List.of("""
A:AA{ .m: Int }
Int:{}
AA:B,C{}
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void threeSupersPickedByOwnMeth(){ok(List.of("""
A:B,C,D{ .m: A }
B:{ .m: B }
C:{ .m: C }
D:{ .m: D }
"""));}
@Test void threeSupersPickedMostSpecific(){ok(List.of("""
A:B,C,D{ .m: B }
B:D{ .m: D }
C:D{ .m: D }
D:{ .m: D }
"""));}
@Test void threeSupersPickedLessSpecific(){fail("""
001| A:B,C,D{ .m: D }
   | ---------^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "D".
But "B.m" returns type "B", which is not a supertype of "D".
It is instead a subtype: you are weakening the result instead of strengthening it.
""", List.of("""
A:B,C,D{ .m: D }
B:D{ .m: B }
C:D{ .m: B }
D:{ .m: B }
"""));}
@Test void sameNameDifferentArities(){fail("""
002| A[X:*]:A[X,X]{ .m(b:A):A }
   | ---------------^^^^^^^^^--

While inspecting type declaration "A[_]"
Invalid method signature for "A[_].m(_)".
The method ".m(_)" returns type "A".
But "A[_,_].m(_)" returns type "A[X,X]", which is not a supertype of "A".
The two types are unrelated.
""", List.of("""
A:A[A],A[A,A]{ .m(a:A):A }
A[X:*]:A[X,X]{ .m(b:A):A }
A[X:*,Y:*]:{ .m(c:A):A[X,Y] }
"""));}
@Test void bothSupersAbstract(){ok(List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo }
C:{ .m(c:Foo): Foo }
"""));}
@Test void firstSuperImplements(){ok(List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo -> b }
C:{ .m(c:Foo): Foo }
"""));}
@Test void secondSuperImplements(){ok(List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo }
C:{ .m(c:Foo): Foo -> c }
"""));}
@Test void bothSupersImplement(){failWf("""
002| A:B,C{}
   | ^^^^^^^

While inspecting type declaration "A"
Ambiguous implementation for method ".m(_)" with 1 parameter.
Implemented by the supertypes:
- "B"
- "C"
Type declaration "A" must declare a method ".m(_)" explicitly implementing the desired behaviour.
""", List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo -> b }
C:{ .m(c:Foo): Foo -> c }
"""));}
@Test void reAbstractedImplBesideAnotherImpl(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
C:B{ .m: R; }
D:A,C{}
"""));}
@Test void inheritedImplBesideAnotherImpl(){failWf("""
005| D:A,C{}
   | ^^^^^^^

While inspecting type declaration "D"
Ambiguous implementation for method ".m" with 0 parameters.
Implemented by the supertypes:
- "A"
- "B"
Type declaration "D" must declare a method ".m" explicitly implementing the desired behaviour.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
C:B{}
D:A,C{}
"""));}
@Test void bothSupersInheritTheSameImpl(){ok(List.of("""
Foo:{}
A:B,C{}
B:D{ .m(b:Foo): Foo }
C:D{ .m(c:Foo): Foo }
D:{ .m(d:Foo): Foo -> d }
"""));}
@Test void genericSupersAgreeOnRt(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:{ .m: List[X] }
C[Y:*]:{ .m: Y }
List[T:*]:{}
"""));}
@Test void genericSupersAgreeOnRtAndOnSharedSuper(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[List[X]]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: Y }
List[T:*]:{}
"""));}
@Test void genericSupersDisagreeOnSharedSuperArgs(){failWf("""
001| A:B[A],C[List[A]]{}
   | ^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the signature of method "imm .kk".
Signatures as inherited by type declaration "A":
-       B[A].kk: A
-       C[List[A]].kk: List[A]
"A" must declare method ".kk".
"A.kk" return type must be a subtype of "A" and "List[A]".
No such type is currently visible.
""", List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[X]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: Y }
List[T:*]:{}
"""));}
@Test void genericSupersDisagreeButSharedMethIsConcrete(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[X]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: A }
List[T:*]:{}
"""));}
@Test void genericSupersAgreeAndSharedMethIsConcrete(){ok(List.of("""
A:B[A],C[List[A]]{}
B[X:*]:K[List[X]]{ .m: List[X] }
C[Y:*]:K[Y]{ .m: Y }
K[Y:*]:{ .kk: A }
List[T:*]:{}
"""));}
@Test void overrideInheritsTheSuperTypeParameters(){ok(List.of("""
Foo:{}
A:B{ .m: Foo }
B:{ .m[X:*]: Foo }
C:{ .withTArg(a:A): Foo -> a.m[Foo]; .noTArg(a:A): Foo -> a.m }
"""));}
@Test void overrideCanNotNameTheInheritedTypeParameter(){failWf("""
002| A:B{ .m(x: X): Foo }
   |            ^

While inspecting a type name
Type "X" is not declared in package "p" and is not made visible via "use".
In scope:
- "A"
- "B"
- "Foo"
""", List.of("""
Foo:{}
A:B{ .m(x: X): Foo }
B:{ .m[X:*](x: X): Foo }
"""));}
@Test void overrideDeclaresTooManyTypeParametersForTwoSupertypes(){failWf("""
002| A:B,C{ .m[X:*,Y:*]: Foo }
   |        ^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" declares 2 generic type parameters, but these supertypes declare 1:
- "B"
- "C"
""", List.of("""
Foo:{}
A:B,C{ .m[X:*,Y:*]: Foo }
B:{ .m[X:*]: Foo }
C:{ .m[Z:*]: Foo }
"""));}
@Test void aMethodUsingTheImplicitParameterWithNoSupertype(){failWf("""
001| A:{ .m -> ::.foo }
   | ----^^^^^^^^^^^^--

While inspecting type declaration "A"
Cannot infer signature of method ".m(_)".
No supertype has a method named ".m(_)" with 1 parameter.
"::" in the body is the parameter of ".m(_)".
""", List.of("""
A:{ .m -> ::.foo }
"""));}
@Test void aMethodUsingAWrittenParameterWithNoSupertype(){failWf("""
001| A:{ .m(x) -> { .k -> ::.foo } }
   | ----^^^^^^^^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "A"
Cannot infer signature of method ".m(_)".
No supertype has a method named ".m(_)" with 1 parameter.
""", List.of("""
A:{ .m(x) -> { .k -> ::.foo } }
"""));}
@Test void overrideDeclaresTooManyTypeParameters(){failWf("""
002| A:B{ .m[X:*,Y:*]: Foo }
   |      ^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" declares 2 generic type parameters, but supertype "B" declares 1.
""", List.of("""
Foo:{}
A:B{ .m[X:*,Y:*]: Foo }
B:{ .m[X:*]: Foo }
"""));}
@Test void overrideDeclaresNarrowerBounds(){failWf("""
002| A:B{ .m[X:imm]: Foo }
   |      ^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" declares different capability bounds than the supertypes for generic type parameter 1.
Local declaration: "X:imm".
Capability bounds in the supertypes: "imm,mut,read".
Generic type parameter names may differ from the supertypes; only the position matters.
""", List.of("""
Foo:{}
A:B{ .m[X:imm]: Foo }
B:{ .m[X:*]: Foo }
"""));}
@Test void classGenericUsedInRefinedRt(){ok(List.of("""
A[X:*]:B{ .foo: imm X }
B:{ .m[X:*]: A[B] }
"""));}
@Test void classGenericPassedToSuperGeneric(){ok(List.of("""
A[X:*]:B[X]{ .foo: imm X }
B[Y:*]:{ .m[X:*]: Bi[imm X,imm Y] }
Bi[AA:*,BB:*]:{}
"""));}
@Test void refineRtGenericArgCovariantIsNotEnough(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{}
"""));}
@Test void refineRtGenericArgContravariant(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{}
"""));}
@Test void refineRtGenericArgCovariantWithGetter(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{ .b: X }
"""));}
@Test void refineRtGenericArgContravariantWithGetter(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{ .b: X }
"""));}
@Test void refineRtGenericArgCovariantRecursive(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{ .b: Break[X] }
"""));}
@Test void refineRtGenericArgContravariantRecursive(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.
""", List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{ .b: Break[X] }
"""));}
@Test void methGens(){ok(List.of("""
A:{
  .m1[T:*](x:T):base.Void->this.m2(x);
  .m2[K:*](k:K):base.Void;
  }
"""));}
@Test void boolPkg(){ok(List.of("""
Bool:Sealed{
  .and(b: Bool): Bool;
  .or(b: Bool): Bool;
  .not: Bool;
  ?[R:*](f: mut ThenElse[R]): R;
  }
Sealed:{}
True:Bool{ .and(b) -> b; .or(b) -> this; .not -> False; ?(f) -> f.then }
False:Bool{ .and(b) -> this; .or(b) -> b; .not -> True; ?(f) -> f.else }
Fresh1:False,Bool{}
Fresh2:Bool,False{}
ThenElse[R:*]:{ mut .then: R; mut .else: R }
"""));}
@Test void namedLiteralKeepsClassGeneric(){ok(List.of("""
List[T:*]:{} Bob:{}
Bar[X:*]:{ .m: Foo[X] -> Foo[X:*]:{} }
"""));}
@Test void genericConflict(){failWf("""
004| D:B,C{}
   | ^^^^^^^

While inspecting type declaration "D"
Supertypes disagree on the signature of method "imm .m(_)".
Signatures as inherited by type declaration "D":
-       B.m(base.Int): base.Int
-       C.m(base.Float): base.Float
No type currently visible is a subtype of the return types: "base.Int" and "base.Float".
"base.Int" is sealed, so no type outside package "base" can implement "base.Int".
Type declaration "D" cannot implement all of those supertypes.
""", List.of("""
A[X:*]:{ .m(x:X):X->x }
B:A[base.Int]{}
C:A[base.Float]{}
D:B,C{}
"""));}
@Test void reAbstractedMethodListingBothSupers(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
C:A,B{}
"""));}
@Test void reAbstractedMethodListingBothSupersSubFirst(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
C:B,A{}
"""));}
@Test void overriddenMethodListingBothSupers(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A->A }
C:A,B{}
"""));}
@Test void reAbstractedMethodAndInheritedImplementation(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
D:A{}
C:B,D{}
"""));}
@Test void reAbstractedMethodAndInheritedImplementationIsAbstract(){fail("""
004| User:{ #:C->C:B,D{} }
   |        -----^^^^^^^

While inspecting object literal "C" > method "User#" (line 4)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "B".
Add an implementation for ".m" inside the object literal.
""", List.of("""
A:{ .m:A->this }
B:A{ .m:A }
D:A{}
User:{ #:C->C:B,D{} }
"""));}
@Test void reAbstractedMethodAndInheritedImplementationSubLast(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
D:A{}
C:D,B{}
"""));}
@Test void reAbstractedDeepInOneBranch(){fail("""
007| User:{ #:D->D:E,F{} }
   |        -----^^^^^^^

While inspecting object literal "D" > method "User#" (line 7)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "C".
Add an implementation for ".m" inside the object literal.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:A{}
C:B{ .m: R; }
E:C{}
F:A{}
User:{ #:D->D:E,F{} }
"""));}
@Test void reAbstractedSuperBesideImpl(){ok(List.of("""
R:{}
A:{ .m: R -> R }
X:A{ .m: R; }
B:{ .m: R -> R }
User:{ #:D->D:X,B{} }
"""));}
@Test void reAbstractedSuperBesideImplImplFirst(){ok(List.of("""
R:{}
A:{ .m: R -> R }
X:A{ .m: R; }
B:{ .m: R -> R }
User:{ #:D->D:B,X{} }
"""));}
@Test void abstractSuperBesideImplIsInstantiable(){ok(List.of("""
R:{}
B:{ .m: R -> R }
C:{ .m: R; }
User:{ #:A->A:B,C{} }
"""));}
@Test void implBesideTwoAbstractSupers(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R; }
C:{ .m: R; }
User:{ #:D->D:B,A,C{} }
"""));}
@Test void reAbstractedImplHiddenInsideAnotherSuper(){ok(List.of("""
R:{}
J:{ .m: R -> R }
X:J{ .m: R; }
I:{ .m: R -> R }
P:X,I{}
Q:J{}
User:{ #:D->D:P,Q{} }
"""));}
@Test void reAbstractedImplHiddenInsideAnotherAbstractSuper(){fail("""
007| User:{ #:D->D:P,Q{} }
   |        -----^^^^^^^

While inspecting object literal "D" > method "User#" (line 7)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "P" and "K" and "X".
Add an implementation for ".m" inside the object literal.
""", List.of("""
R:{}
J:{ .m: R -> R }
X:J{ .m: R; }
K:{ .m: R; }
P:X,K{}
Q:J{}
User:{ #:D->D:P,Q{} }
"""));}
@Test void eachImplReAbstractedByTheOtherBranch(){fail("""
006| User:{ #:D->D:A1,A2{} }
   |        -----^^^^^^^^^

While inspecting object literal "D" > method "User#" (line 6)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "A1" and "A2".
Add an implementation for ".m" inside the object literal.
""", List.of("""
R:{}
I1:{ .m: R -> R }
I2:{ .m: R -> R }
A1:I2{ .m: R; }
A2:I1{ .m: R; }
User:{ #:D->D:A1,A2{} }
"""));}
@Test void eachImplReAbstractedByTheOtherBranchDeclared(){ok(List.of("""
R:{}
I1:{ .m: R -> R }
I2:{ .m: R -> R }
A1:I2{ .m: R; }
A2:I1{ .m: R; }
D:A1,A2{}
"""));}
@Test void implOverriddenByImplInAnotherBranch(){ok(List.of("""
R:{}
J:{ .m: R -> R }
K:J{ .m: R -> R }
Q:J{}
User:{ #:D->D:Q,K{} }
"""));}
@Test void reAbstractedThenReImplementedInAnotherBranch(){ok(List.of("""
R:{}
A:{ .m: R -> R }
X:A{ .m: R; }
Z:A{ .m: R -> R }
User:{ #:D->D:X,Z{} }
"""));}
@Test void reImplementedBelowReAbstraction(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:A{ .m: R; }
C:B{ .m: R -> R }
E:A{}
User:{ #:D->D:E,C{} }
"""));}
@Test void twoImplsReAbstractedTogetherBesideAThird(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
X:A,B{ .m: R; }
C:{ .m: R -> R }
User:{ #:D->D:X,C{} }
"""));}
@Test void oneReAbstractedTwoLeftAmbiguous(){failWf("""
006| D:X,B,C{}
   | ^^^^^^^^^

While inspecting type declaration "D"
Ambiguous implementation for method ".m" with 0 parameters.
Implemented by the supertypes:
- "B"
- "C"
Type declaration "D" must declare a method ".m" explicitly implementing the desired behaviour.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
C:{ .m: R -> R }
X:A{ .m: R; }
D:X,B,C{}
"""));}
@Test void reAbstractedOnlyInAnUnrelatedBranch(){failWf("""
006| D:X,B{}
   | ^^^^^^^

While inspecting type declaration "D"
Ambiguous implementation for method ".m" with 0 parameters.
Implemented by the supertypes:
- "A"
- "B"
Type declaration "D" must declare a method ".m" explicitly implementing the desired behaviour.
""", List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
Y:{ .m: R; }
X:A,Y{}
D:X,B{}
"""));}
@Test void ambiguityResolvedByOwnMethod(){ok(List.of("""
R:{}
A:{ .m: R -> R }
B:{ .m: R -> R }
X:A{}
User:{ #:D->D:X,B{ .m->R } }
"""));}
@Test void reAbstractedOtherCapabilityKeepsImpl(){ok(List.of("""
R:{}
A:{ imm .m: R -> R; mut .m: R -> R }
X:A{ mut .m: R; }
B:{ mut .m: R -> R }
User:{ #:mut D->D:X,B{} }
"""));}
@Test void reAbstractedMethodInNestedDeclaration(){fail("""
003| User:{ #:C->C:A,B{} }
   |        -----^^^^^^^

While inspecting object literal "C" > method "User#" (line 3)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "B".
Add an implementation for ".m" inside the object literal.
""", List.of("""
A:{ .m:A->this }
B:A{ .m:A }
User:{ #:C->C:A,B{} }
"""));}
@Test void reAbstractedMethodInNestedDeclarationOnlySubSuper(){fail("""
003| User:{ #:C->C:B{} }
   |        -----^^^^^

While inspecting object literal "C" > method "User#" (line 3)
This object literal is missing a required method.
Missing: "imm .m".
Required by: "B".
Add an implementation for ".m" inside the object literal.
""", List.of("""
A:{ .m:A->this }
B:A{ .m:A }
User:{ #:C->C:B{} }
"""));}
@Test void reAbstractedMethodImplementedInNestedDeclaration(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
User:{ #:C->C:A,B{ .m->A } }
"""));}
@Test void reAbstractedMethodListingOnlySubSuper(){ok(List.of("""
A:{ .m:A->this }
B:A{ .m:A }
C:B{}
"""));}
@Test void overrideRefinesMutResultKeepingCapability(){ok(List.of("""
P:{}
Q:P{}
Sup:{ mut .h: mut P }
Sub:Sup{ mut .h: mut Q }
"""));}
@Test void overrideWeakensParamKeepingCapability(){ok(List.of("""
P:{}
Q:P{}
Sup:{ .g(x: mut Q): P }
Sub:Sup{ .g(x: mut P): P }
"""));}
@Test void overrideSpellsRedundantCapabilityOnTypeVariable(){ok(List.of("""
Sup[X:mut]:{ .h(x: X): X }
Sub[X:mut]:Sup[X]{ .h(x: mut X): mut X }
"""));}
@Test void overrideSpellsRedundantReadImmOnTypeVariable(){ok(List.of("""
Sup[X:imm]:{ .h(x: X): X }
Sub[X:imm]:Sup[X]{ .h(x: read/imm X): read/imm X }
"""));}
@Test void classGenericNarrowerBoundOverrideSpellsReadImm(){ok(List.of("""
Baz:{}
Sup[X:imm,mut]:{ .h(x: X): X }
Sub[Y:imm]:Sup[Y]{ .h(x: read/imm Y): read/imm Y -> x }
User:{ .viaSup(s: Sup[Baz]): Baz -> s.h(Baz); .use: Baz -> this.viaSup(Sub[Baz]) }
"""));}
@Test void overrideStrengthensResultCapability(){fail("""
003| Sub:Sup{ mut .h: iso P }
   | ---------^^^^^^^^^^^^^--

While inspecting type declaration "Sub"
Invalid method signature for "mut Sub.h".
The method ".h" returns type "iso P".
But "mut Sup.h" returns type "mut P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ mut .h: mut P }
Sub:Sup{ mut .h: iso P }
"""));}
@Test void overrideWeakensParamCapability(){fail("""
003| Sub:Sup{ .g(x: read P): P }
   | ---------^^^^^^^^^^^^^^^^--

While inspecting type declaration "Sub"
Invalid method signature for "Sub.g(_)".
The method ".g(_)" accepts parameter 1 of type "read P".
But "Sup.g(_)" requires "mut P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ .g(x: mut P): P }
Sub:Sup{ .g(x: read P): P }
"""));}
@Test void overrideChangesHygienicParamCapability(){fail("""
003| Sub:Sup{ .g(x: readH P): P }
   | ---------^^^^^^^^^^^^^^^^^--

While inspecting type declaration "Sub"
Invalid method signature for "Sub.g(_)".
The method ".g(_)" accepts parameter 1 of type "readH P".
But "Sup.g(_)" requires "mutH P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ .g(x: mutH P): P }
Sub:Sup{ .g(x: readH P): P }
"""));}
@Test void overrideDropsReadImmOnTypeVariable(){fail("""
002| Sub[X:*]:Sup[X]{ .h(x: X): X }
   | -----------------^^^^^^^^^^^--

While inspecting type declaration "Sub[_]"
Invalid method signature for "Sub[_].h(_)".
The method ".h(_)" returns type "X".
But "Sup[_].h(_)" returns type "read/imm X".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
Sup[X:*]:{ .h(x: X): read/imm X }
Sub[X:*]:Sup[X]{ .h(x: X): X }
"""));}
@Test void overrideInLiteralStrengthensResultCapability(){fail("""
003| User:{ #: mut Sup -> mut Sup{ mut .h: iso P -> P } }
   |        --------------~~~~~~~~~^^^^^^^^^^^^^^^^^^~~

While inspecting object literal instance of "Sup" > method "User#" (line 3)
Invalid method signature for "mut Sup.h".
The method ".h" returns type "iso P".
But "mut Sup.h" returns type "mut P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
P:{}
Sup:{ mut .h: mut P }
User:{ #: mut Sup -> mut Sup{ mut .h: iso P -> P } }
"""));}
@Test void genericTwiceDifferingInCapabilityUnused(){ok(List.of("""
Bar:{}
Beer:{}
Foo[T:*]:{}
A:Foo[imm Bar],Foo[mut Beer]{}
"""));}
@Test void genericTwiceDifferingInNominalTypeRefinedToCommonSubtype(){ok(List.of("""
Bar:{}
Beer:{}
Both:Bar,Beer{}
Foo[T:*]:{ .get: T }
A:Foo[Bar],Foo[Beer]{ .get: Both -> Both }
"""));}
@Test void genericTwiceDifferingInCapabilityCanNotBeOverridden(){fail("""
005| A:Foo[imm Bar],Foo[mut Beer]{ .get: Both -> Both }
   | ------------------------------^^^^^^^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature for "A.get".
The method ".get" returns type "imm Both".
But "Foo[_].get" returns type "mut Beer".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
Bar:{}
Beer:{}
Both:Bar,Beer{}
Foo[T:*]:{ .get: T }
A:Foo[imm Bar],Foo[mut Beer]{ .get: Both -> Both }
"""));}
@Test void genericTwiceDifferingInCapabilityInherited(){failWf("""
004| A:Foo[imm Bar],Foo[mut Beer]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A":
-       Foo[Bar].get: Bar
-       Foo[mut Beer].get: mut Beer
The return type differs in reference capability; overriding must keep the reference capability.
Type declaration "A" cannot implement all of those supertypes.
""", List.of("""
Bar:{}
Beer:{}
Foo[T:*]:{ .get: T }
A:Foo[imm Bar],Foo[mut Beer]{}
"""));}
@Test void overrideDropsImmOnTypeVariable(){fail("""
002| Sub[X:*]:Sup[X]{ .h(x: X): X }
   | -----------------^^^^^^^^^^^--

While inspecting type declaration "Sub[_]"
Invalid method signature for "Sub[_].h(_)".
The method ".h(_)" returns type "X".
But "Sup[_].h(_)" returns type "imm X".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.
""", List.of("""
Sup[X:*]:{ .h(x: X): imm X }
Sub[X:*]:Sup[X]{ .h(x: X): X }
"""));}
@Test void genericTwiceDifferingInCapabilityViaInexactBound(){failWf("""
002| A[Y:imm,mut]:Foo[Y],Foo[imm Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A[_]":
-       Foo[Y].get: Y
-       Foo[imm Y].get: imm Y
The return type differs in reference capability; overriding must keep the reference capability.
Type declaration "A[_]" cannot implement all of those supertypes.
""", List.of("""
Foo[T:*]:{ .get: T }
A[Y:imm,mut]:Foo[Y],Foo[imm Y]{}
"""));}
@Test void methodGenericSameCapabilityViaExactBoundInherited(){ok(List.of("""
Baz:{}
Foo:{ .get[T:mut]: T }
Bar:{ .get[T:mut]: mut T }
A:Foo,Bar{}
User:{ #(a: A): mut Baz -> a.get[mut Baz] }
"""));}
@Test void methodGenericSameReadImmViaExactBoundInherited(){ok(List.of("""
Baz:{}
Foo:{ .get[T:imm]: T }
Bar:{ .get[T:imm]: read/imm T }
A:Foo,Bar{}
User:{ #(a: A): Baz -> a.get[Baz] }
"""));}
@Test void classGenericSameReadImmViaExactBoundInherited(){ok(List.of("""
Foo[X:imm]:{ .get: X }
Bar[X:imm]:{ .get: read/imm X }
A[Y:imm]:Foo[Y],Bar[Y]{}
"""));}
@Test void classGenericAgainstNominalWithTheSameCapabilityInherited(){failWf("""
003| A[Y:imm]:Foo[Y],Foo[Bar]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A[_]":
-       Foo[Y].get: Y
-       Foo[Bar].get: Bar
The return type differs, and "Y" is a generic type parameter: no type can be a subtype of "Y" and "Bar".
Type declaration "A[_]" cannot implement all of those supertypes.
""", List.of("""
Bar:{}
Foo[T:*]:{ .get: T }
A[Y:imm]:Foo[Y],Foo[Bar]{}
"""));}
@Test void classGenericAgainstNominalWithADifferentCapabilityInherited(){failWf("""
003| A[Y:imm,mut]:Foo[Y],Foo[Bar]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A[_]":
-       Foo[Y].get: Y
-       Foo[Bar].get: Bar
The return type differs, and "Y" is a generic type parameter: no type can be a subtype of "Y" and "Bar".
Type declaration "A[_]" cannot implement all of those supertypes.
""", List.of("""
Bar:{}
Foo[T:*]:{ .get: T }
A[Y:imm,mut]:Foo[Y],Foo[Bar]{}
"""));}
@Test void classGenericNarrowerBoundSameReadImmInherited(){ok(List.of("""
Baz:{}
Foo[X:imm,mut]:{ .get: X }
Bar[X:imm,mut]:{ .get: read/imm X }
A[Y:imm]:Foo[Y],Bar[Y]{}
Make:{ #[Y:imm](y: Y): A[Y] -> { .get -> y } }
User:{
  .viaA[Z:imm](a: A[Z]): Z -> a.get;
  .asFoo[Z:imm](a: A[Z]): Foo[Z] -> a;
  .asBar[Z:imm](a: A[Z]): Bar[Z] -> a;
  .viaFoo(a: A[Baz]): Baz -> this.asFoo(a).get;
  .viaBar(a: A[Baz]): Baz -> this.asBar(a).get;
  .use: Baz -> this.viaBar(Make#Baz);
}
"""));}
@Test void classGenericNarrowerBoundSupertypeImpliedWithRedundantRc(){ok(List.of("""
Baz:{}
Foo[T:*]:{ .get: T }
Bar[X:imm,mut]:Foo[imm X]{}
A[Y:imm]:Foo[Y],Bar[Y]{}
User:{ .asFoo(a: A[Baz]): Foo[Baz] -> a; .get(a: A[Baz]): Baz -> a.get; .make: A[Baz] -> { .get -> Baz } }
"""));}
@Test void classGenericSameBoundDifferingReadImmInherited(){failWf("""
003| A[Y:imm,mut]:Foo[Y],Bar[Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A[_]":
-       Foo[Y].get: Y
-       Bar[Y].get: read/imm Y
The return type differs in reference capability; overriding must keep the reference capability.
Type declaration "A[_]" cannot implement all of those supertypes.
""", List.of("""
Foo[X:imm,mut]:{ .get: X }
Bar[X:imm,mut]:{ .get: read/imm X }
A[Y:imm,mut]:Foo[Y],Bar[Y]{}
"""));}
@Test void methodGenericSameReadViaExactBoundInherited(){ok(List.of("""
Baz:{}
Foo:{ .get[T:mut](t: read T): Baz }
Bar:{ .get[T:mut](t: read/imm T): Baz }
A:Foo,Bar{}
"""));}
@Test void methodGenericDifferingReadImmViaExactBoundInherited(){failWf("""
003| A:Foo,Bar{}
   | ^^^^^^^^^^^

While inspecting type declaration "A"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A":
-       Foo.get[T:mut]: T
-       Bar.get[T:mut]: read/imm T
The return type differs in reference capability; overriding must keep the reference capability.
Type declaration "A" cannot implement all of those supertypes.
""", List.of("""
Foo:{ .get[T:mut]: T }
Bar:{ .get[T:mut]: read/imm T }
A:Foo,Bar{}
"""));}
@Test void methodGenericSameCapabilityViaExactBoundOverridden(){ok(List.of("""
Foo:{ .get[T:mut]: T }
Bar:{ .get[T:mut]: mut T }
A:Foo,Bar{ .get[T:mut]: T }
"""));}
@Test void methodGenericSameCapabilityViaExactBoundArgument(){ok(List.of("""
Baz:{}
Foo:{ .set[T:read](t: T): Baz }
Bar:{ .set[T:read](t: read T): Baz }
A:Foo,Bar{}
"""));}
@Test void methodGenericSameCapabilityViaExactBoundNested(){ok(List.of("""
Box[T:*]:{}
Foo:{ .get[T:mut]: Box[T] }
Bar:{ .get[T:mut]: Box[mut T] }
A:Foo,Bar{}
"""));}
@Test void overrideBoundsAreComparedByPositionNotByName(){failWf("""
002| C:A{.m[Y:imm,X:imm](x:Y,y:X):Y->x}
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "C"
Invalid method signature for "C.m(_,_)".
The method ".m(_,_)" declares different capability bounds than the supertypes for generic type parameter 2.
Local declaration: "X:imm".
Capability bounds in the supertypes: "mut".
Generic type parameter names may differ from the supertypes; only the position matters.
""", List.of("""
A:{.m[X:imm,Y:mut](x:X,y:Y):X}
C:A{.m[Y:imm,X:imm](x:Y,y:X):Y->x}
"""));}
@Test void supertypesDisagreeOnBoundsInsideAGenericMethod(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .id(_)".
Original signatures:
-       Sup1.id[X](X): X
-       Sup2.id[X:read](X): X
Signatures as inherited by object literal "Both":
-       Sup1.id[_AX](_AX): _AX
-       Sup2.id[_BX:read](_BX): _BX
The capability bounds of generic type parameter 1 differ; overriding must keep the capability bounds.
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .id[X:imm](x:X):X }
Sup2:{ .id[X:read](x:X):X }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithTheGenericOfTheSecondSupertype(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .get".
Original signatures:
-       Sup1.get[X]: Sup2
-       Sup2.get[X]: X
Signatures as inherited by object literal "Both":
-       Sup1.get[_AX]: Sup2
-       Sup2.get[_AX]: _AX
The return type differs, and "_AX" is a generic type parameter: no type can be a subtype of "Sup2" and "_AX".
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .get[X]:Sup2 }
Sup2:{ .get[X]:X }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAGenericMatchedByPosition(){failWf("""
003| A:{ .m[Y](y:Y): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .get".
Original signatures:
-       Sup1.get[X]: Sup1
-       Sup2.get[Y]: Y
Signatures as inherited by object literal "Both":
-       Sup1.get[X]: Sup1
-       Sup2.get[X]: X
The return type differs, and "X" is a generic type parameter: no type can be a subtype of "Sup1" and "X".
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .get[X]:Sup1 }
Sup2:{ .get[Y]:Y }
A:{ .m[Y](y:Y): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnTheReturnTypeInsideAGenericMethod(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .get".
Original signatures:
-       Sup1.get[X]: X
-       Sup2.get[X]: Sup1
Signatures as inherited by object literal "Both":
-       Sup1.get[_AX]: _AX
-       Sup2.get[_AX]: Sup1
The return type differs, and "_AX" is a generic type parameter: no type can be a subtype of "_AX" and "Sup1".
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .get[X]:X }
Sup2:{ .get[X]:Sup1 }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAReturnTypeImplementingTheOther(){failWf("""
005| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Q1
-       S2.foo: Q2
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Q1" and "Q2".
Such type currently visible: "Q1".
""", List.of("""
Q2:{}
Q1:Q2{}
S1:{ .foo: Q1 }
S2:{ .foo: Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAnExistingCommonSubtype(){failWf("""
007| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: mut Q1
-       S2.foo: mut Q2
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "mut Q1" and "mut Q2".
Such types currently visible:
- "mut Q12"
- "mut Q123"
""", List.of("""
Q1:{}
Q2:{}
Q12:Q1,Q2{}
Q123:Q12{}
S1:{ .foo: mut Q1 }
S2:{ .foo: mut Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnAParameterTypeWithACommonSupertype(){failWf("""
006| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): S1
-       S2.foo(Q2): S1
"B" must declare method ".foo(_)".
"B.foo(_)" parameter 1 type must be a supertype of "Q1" and "Q2".
Such type currently visible: "Q0".
""", List.of("""
Q0:{}
Q1:Q0{}
Q2:Q0{}
S1:{ .foo(x: Q1): S1 }
S2:{ .foo(x: Q2): S1 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnAParameterTypeImplementedByTheOther(){failWf("""
005| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): S1
-       S2.foo(Q2): S1
"B" must declare method ".foo(_)".
"B.foo(_)" parameter 1 type must be a supertype of "Q1" and "Q2".
Such type currently visible: "Q2".
""", List.of("""
Q2:{}
Q1:Q2{}
S1:{ .foo(x: Q1): S1 }
S2:{ .foo(x: Q2): S1 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnAParameterTypeAndOnTheReturnType(){failWf("""
006| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): Q1
-       S2.foo(Q2): Q2
"B" must declare method ".foo(_)".
"B.foo(_)" parameter 1 type must be a supertype of "Q1" and "Q2".
Such type currently visible: "Q0".
"B.foo(_)" return type must be a subtype of "Q1" and "Q2".
No such type is currently visible.
""", List.of("""
Q0:{}
Q1:Q0{}
Q2:Q0{}
S1:{ .foo(x: Q1): Q1 }
S2:{ .foo(x: Q2): Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWhenTheParameterTypeIsWritten(){failWf("""
006| B:S1,S2{ .foo(x: Q0) -> this.foo(x) }
   |          ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): Q1
-       S2.foo(Q2): Q2
"B.foo(_)" must declare the return type.
"B.foo(_)" return type must be a subtype of "Q1" and "Q2".
No such type is currently visible.
""", List.of("""
Q0:{}
Q1:Q0{}
Q2:Q0{}
S1:{ .foo(x: Q1): Q1 }
S2:{ .foo(x: Q2): Q2 }
B:S1,S2{ .foo(x: Q0) -> this.foo(x) }
"""));}
@Test void supertypesAgreeWhenTheWrittenSignatureChoosesTheTypes(){ok(List.of("""
Q0:{}
Q1:Q0{}
Q2:Q0{}
Q12:Q1,Q2{}
S1:{ .foo(x: Q1): Q1 }
S2:{ .foo(x: Q2): Q2 }
B:S1,S2{ .foo(x: Q0): Q12 -> this.foo(x) }
"""));}
@Test void supertypesDisagreeOnASealedReturnTypeOfAnotherPackage(){failWf("""
003| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: base.Nat
-       S2.foo: base.Str
No type currently visible is a subtype of the return types: "base.Nat" and "base.Str".
"base.Nat" is sealed, so no type outside package "base" can implement "base.Nat".
Type declaration "B" cannot implement all of those supertypes.
""", List.of("""
S1:{ .foo: base.Nat }
S2:{ .foo: base.Str }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeOfMutMethods(){failWf("""
005| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "mut .foo".
Signatures as inherited by type declaration "B":
-   mut S1.foo: Q1
-   mut S2.foo: Q2
"B" must declare method "mut .foo".
"B.foo" return type must be a subtype of "Q1" and "Q2".
No such type is currently visible.
""", List.of("""
Q1:{}
Q2:{}
S1:{ mut .foo: Q1 }
S2:{ mut .foo: Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheBoundsOfTheSecondGenericTypeParameter(){failWf("""
003| B:Sup1,Sup2{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .id(_)".
Signatures as inherited by type declaration "B":
-       Sup1.id[X,Y](X): X
-       Sup2.id[X,Y:read](X): X
The capability bounds of generic type parameter 2 differ; overriding must keep the capability bounds.
Type declaration "B" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .id[X,Y](x:X):X }
Sup2:{ .id[X,Y:read](x:X):X }
B:Sup1,Sup2{}
"""));}
@Test void supertypesDisagreeOnTheCapabilityOfAParameterType(){failWf("""
004| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(mut Q): S1
-       S2.foo(read Q): S1
The type of parameter 1 differs in reference capability; overriding must keep the reference capability.
Type declaration "B" cannot implement all of those supertypes.
""", List.of("""
Q:{}
S1:{ .foo(x: mut Q): S1 }
S2:{ .foo(x: read Q): S1 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnAParameterTypeThatIsAGenericTypeParameter(){failWf("""
003| A[Y:imm]:Foo[Y],Foo[Bar]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the signature of method "imm .set(_)".
Signatures as inherited by type declaration "A[_]":
-       Foo[Y].set(Y): Bar
-       Foo[Bar].set(Bar): Bar
The type of parameter 1 differs, and "Y" is a generic type parameter: no type can be a supertype of "Y" and "Bar".
Type declaration "A[_]" cannot implement all of those supertypes.
""", List.of("""
Bar:{}
Foo[T:*]:{ .set(t: T): Bar }
A[Y:imm]:Foo[Y],Foo[Bar]{}
"""));}
@Test void supertypesDisagreeOnTwoTypesTheWrittenMethodLeavesOut(){failWf("""
006| B:S1,S2{ .foo(x) -> this.foo(x) }
   |          ^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): Q1
-       S2.foo(Q2): Q2
"B.foo(_)" must declare the type of parameter 1 and the return type.
"B.foo(_)" parameter 1 type must be a supertype of "Q1" and "Q2".
Such type currently visible: "Q0".
"B.foo(_)" return type must be a subtype of "Q1" and "Q2".
No such type is currently visible.
""", List.of("""
Q0:{}
Q1:Q0{}
Q2:Q0{}
S1:{ .foo(x: Q1): Q1 }
S2:{ .foo(x: Q2): Q2 }
B:S1,S2{ .foo(x) -> this.foo(x) }
"""));}
@Test void supertypesDisagreeOnASealedReturnTypeThatIsNotTheFirst(){failWf("""
004| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Q
-       S2.foo: base.Nat
No type currently visible is a subtype of the return types: "Q" and "base.Nat".
"base.Nat" is sealed, so no type outside package "base" can implement "base.Nat".
Type declaration "B" cannot implement all of those supertypes.
""", List.of("""
Q:{}
S1:{ .foo: Q }
S2:{ .foo: base.Nat }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnASealedReturnTypeWithAVisibleSubtype(){failWf("""
003| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: base.Bool
-       S2.foo: base.True
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "base.Bool" and "base.True".
Such type currently visible: "base.True".
""", List.of("""
S1:{ .foo: base.Bool }
S2:{ .foo: base.True }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnBoundsOfAMethodInheritedThroughAGenericSupertype(){failWf("""
004| D[Y:*]:Mid[Y],Other{}
   | ^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "D[_]"
Supertypes disagree on the signature of method "imm .id(_)".
Original signatures:
-       Sup.id[X](X): X
-       Other.id[Y:read](Y): Y
Signatures as inherited by type declaration "D[_]":
-       Mid[Y].id[_AX](_AX): _AX
-       Other.id[_AY:read](_AY): _AY
The capability bounds of generic type parameter 1 differ; overriding must keep the capability bounds.
Type declaration "D[_]" cannot implement all of those supertypes.
""", List.of("""
Sup:{ .id[X](x:X):X }
Mid[X:*]:Sup{}
Other:{ .id[Y:read](y:Y):Y }
D[Y:*]:Mid[Y],Other{}
"""));}
@Test void supertypesDisagreeOnAParameterTypeDeclaredAfterTheLiteral(){failWf("""
001| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): S1
-       S2.foo(Q2): S1
"B" must declare method ".foo(_)".
"B.foo(_)" parameter 1 type must be a supertype of "Q1" and "Q2".
Such type currently visible: "Q2".
""", List.of("""
B:S1,S2{}
Q2:{}
Q1:Q2{}
S1:{ .foo(x: Q1): S1 }
S2:{ .foo(x: Q2): S1 }
"""));}
@Test void supertypesDisagreeOnReturnTypesWithTheSameGenericType(){failWf("""
006| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Foo[Q1]
-       S2.foo: Foo[Q2]
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Foo[Q1]" and "Foo[Q2]".
No such type is currently visible.
""", List.of("""
Q1:{}
Q2:{}
Foo[T:*]:{ .get: T }
S1:{ .foo: Foo[Q1] }
S2:{ .foo: Foo[Q2] }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnReturnTypesWithTheSameGenericTypeImplementedByAGenericType(){failWf("""
007| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Foo[Q1]
-       S2.foo: Foo[Q2]
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Foo[Q1]" and "Foo[Q2]".
No such type is currently visible.
""", List.of("""
Q1:{}
Q2:{}
Foo[T:*]:{ .get: T }
G[T:*]:Foo[T]{}
S1:{ .foo: Foo[Q1] }
S2:{ .foo: Foo[Q2] }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnReturnTypesWithTheSameGenericTypeImplementedWithBothArguments(){failWf("""
008| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Foo[Q1]
-       S2.foo: Foo[Q2]
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Foo[Q1]" and "Foo[Q2]".
Such types currently visible:
- "G[Q2]"
- "K"
""", List.of("""
Q1:{}
Q2:{}
Foo[T:*]:{}
K:Foo[Q1],Foo[Q2]{}
G[T:*]:Foo[Q1],Foo[T]{}
S1:{ .foo: Foo[Q1] }
S2:{ .foo: Foo[Q2] }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAGenericSubtypeFixingOneTypeArgument(){failWf("""
007| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Foo[Q1]
-       S2.foo: Bar
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Foo[Q1]" and "Bar".
Such type currently visible: "G[Q1,_]".
""", List.of("""
Q1:{}
Bar:{}
Foo[T:*]:{}
G[T:*,U:*]:Foo[T],Bar{}
S1:{ .foo: Foo[Q1] }
S2:{ .foo: Bar }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAGenericSubtypeWhoseBoundRejectsTheArgument(){failWf("""
007| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Foo[mut Q1]
-       S2.foo: Bar
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Foo[mut Q1]" and "Bar".
No such type is currently visible.
""", List.of("""
Q1:{}
Bar:{}
Foo[T:*]:{}
G[T:imm]:Foo[T],Bar{}
S1:{ .foo: Foo[mut Q1] }
S2:{ .foo: Bar }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAGenericSubtypeNeedingAnotherCapability(){failWf("""
007| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Foo[Q1]
-       S2.foo: Bar
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Foo[Q1]" and "Bar".
Such type currently visible: "G[mut Q1]".
""", List.of("""
Q1:{}
Bar:{}
Foo[T:*]:{}
G[T:mut]:Foo[imm T],Bar{}
S1:{ .foo: Foo[Q1] }
S2:{ .foo: Bar }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithAGenericCommonSubtype(){failWf("""
006| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Q1
-       S2.foo: Q2
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Q1" and "Q2".
Such type currently visible: "Q12[_]".
""", List.of("""
Q1:{}
Q2:{}
Q12[T:*]:Q1,Q2{}
S1:{ .foo: Q1 }
S2:{ .foo: Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeOfAGenericLiteral(){failWf("""
003| B[Y:*]:A1,A2{}
   | ^^^^^^^^^^^^^^

While inspecting type declaration "B[_]"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B[_]":
-       A1.foo: A1
-       A2.foo: A2
"B[_]" must declare method ".foo".
"B[_].foo" return type must be a subtype of "A1" and "A2".
Such type currently visible: "B[_]".
""", List.of("""
A1:{ .foo: A1 }
A2:{ .foo: A2 }
B[Y:*]:A1,A2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithANestedCommonSubtype(){failWf("""
006| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Q1
-       S2.foo: Q2
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Q1" and "Q2".
Such type currently visible: "Q12".
""", List.of("""
Q1:{}
Q2:{}
Holder:{ .h: Q1 -> Q12:Q1,Q2{} }
S1:{ .foo: Q1 }
S2:{ .foo: Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeOfAGenericTypeParameterWithTwoBounds(){failWf("""
003| A[Y:imm,read]:Foo[Y],Bar[Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Supertypes disagree on the signature of method "imm .get".
Signatures as inherited by type declaration "A[_]":
-       Foo[Y].get: Y
-       Bar[Y].get: read/imm Y
The return type differs in reference capability; overriding must keep the reference capability.
Type declaration "A[_]" cannot implement all of those supertypes.
""", List.of("""
Foo[X:imm,read]:{ .get: X }
Bar[X:imm,read]:{ .get: read/imm X }
A[Y:imm,read]:Foo[Y],Bar[Y]{}
"""));}
@Test void supertypesDisagreeOnAMethodMergedInASupertype(){failWf("""
005| A:{ .m[X](x:X): T1 -> Both:Mid,Other{} }
   |                       ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .id(_)".
Original signatures:
-       T1.id[X](X): X
-       T2.id[Y](Y): Y
-       Other.id[Z:read](Z): Z
Signatures as inherited by object literal "Both":
-       Mid.id[_AX](_AX): _AX
-       Other.id[Z:read](Z): Z
The capability bounds of generic type parameter 1 differ; overriding must keep the capability bounds.
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
T1:{ .id[X](x:X):X }
T2:{ .id[Y](y:Y):Y }
Mid:T1,T2{}
Other:{ .id[Z:read](z:Z):Z }
A:{ .m[X](x:X): T1 -> Both:Mid,Other{} }
"""));}
@Test void supertypesDisagreeOnAMethodImplementedWithAnInferredSignature(){failWf("""
004| B[X:*]:Mid[X],Other{}
   | ^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B[_]"
Supertypes disagree on the signature of method "imm .id(_)".
Original signatures:
-       T1.id[X](X): X
-       Other.id[Z:read](Z): Z
Signatures as inherited by type declaration "B[_]":
-       Mid[X].id[_AX](_AX): _AX
-       Other.id[Z:read](Z): Z
The capability bounds of generic type parameter 1 differ; overriding must keep the capability bounds.
Type declaration "B[_]" cannot implement all of those supertypes.
""", List.of("""
T1:{ .id[X](x:X):X }
Mid[X:*]:T1{ .id(x) -> x }
Other:{ .id[Z:read](z:Z):Z }
B[X:*]:Mid[X],Other{}
"""));}
@Test void supertypesDisagreeOnAMethodWrittenWithoutItsGenericTypeParameters(){failWf("""
004| B[Y:*]:Mid[Y],Sup2{}
   | ^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B[_]"
Supertypes disagree on the signature of method "imm .id(_)".
Original signatures:
-       Sup1.id[X](Sup1): Sup1
-       Sup2.id[Y:read](Sup1): Sup1
Signatures as inherited by type declaration "B[_]":
-       Mid[Y].id[_AX](Sup1): Sup1
-       Sup2.id[_AY:read](Sup1): Sup1
The capability bounds of generic type parameter 1 differ; overriding must keep the capability bounds.
Type declaration "B[_]" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .id[X](x:Sup1):Sup1 }
Mid[X:*]:Sup1{ .id(x:Sup1):Sup1 -> x }
Sup2:{ .id[Y:read](y:Sup1):Sup1 }
B[Y:*]:Mid[Y],Sup2{}
"""));}
@Test void supertypesDisagreeOnTheReturnTypeWithManyCommonSubtypes(){failWf("""
012| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Q1
-       S2.foo: Q2
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Q1" and "Q2".
Such types currently visible:
- "C1"
- "C2"
- "C3"
- "C4"
- "C5"
- "C6"
- ... (1 more)
""", List.of("""
Q1:{}
Q2:{}
C1:Q1,Q2{}
C2:Q1,Q2{}
C3:Q1,Q2{}
C4:Q1,Q2{}
C5:Q1,Q2{}
C6:Q1,Q2{}
C7:Q1,Q2{}
S1:{ .foo: Q1 }
S2:{ .foo: Q2 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeOnAParameterTypeWithSeveralCommonSupertypes(){failWf("""
007| B:S1,S2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo(_)".
Signatures as inherited by type declaration "B":
-       S1.foo(Q1): S1
-       S2.foo(Q2): S1
"B" must declare method ".foo(_)".
"B.foo(_)" parameter 1 type must be a supertype of "Q1" and "Q2".
Such types currently visible:
- "Q0"
- "R"
""", List.of("""
R:{}
Q0:R{}
Q1:Q0{}
Q2:Q0{}
S1:{ .foo(x: Q1): S1 }
S2:{ .foo(x: Q2): S1 }
B:S1,S2{}
"""));}
@Test void supertypesDisagreeAmongThreeSupertypes(){failWf("""
007| B:S1,S2,S3{}
   | ^^^^^^^^^^^^

While inspecting type declaration "B"
Supertypes disagree on the signature of method "imm .foo".
Signatures as inherited by type declaration "B":
-       S1.foo: Q1
-       S2.foo: Q2
-       S3.foo: Q3
"B" must declare method ".foo".
"B.foo" return type must be a subtype of "Q1", "Q2" and "Q3".
No such type is currently visible.
""", List.of("""
Q1:{}
Q2:{}
Q3:{}
S1:{ .foo: Q1 }
S2:{ .foo: Q2 }
S3:{ .foo: Q3 }
B:S1,S2,S3{}
"""));}
@Test void supertypesDisagreeOnAGenericReturnTypeInsideAGenericMethod(){failWf("""
005| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .get(_)".
Original signatures:
-       Sup1.get[X](X): Foo[X]
-       Sup2.get[Y](Y): Bar[Y]
Signatures as inherited by object literal "Both":
-       Sup1.get[_AX](_AX): Foo[_AX]
-       Sup2.get[_AX](_AX): Bar[_AX]
"Both" must declare method ".get(_)".
"Both.get(_)" return type must be a subtype of "Foo[_AX]" and "Bar[_AX]".
No such type is currently visible.
""", List.of("""
Foo[T:*]:{}
Bar[T:*]:{}
Sup1:{ .get[X](x:X): Foo[X] }
Sup2:{ .get[Y](y:Y): Bar[Y] }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void supertypesDisagreeOnGenericArityInsideAGenericMethod(){failWf("""
003| A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
   |                         ^^^^^^^^^^^^^^^^

While inspecting object literal "Both"
Supertypes disagree on the signature of method "imm .id(_)".
Original signatures:
-       Sup1.id[X](Sup1): Sup1
-       Sup2.id(Sup1): Sup1
Signatures as inherited by object literal "Both":
-       Sup1.id[_AX](Sup1): Sup1
-       Sup2.id(Sup1): Sup1
The number of generic type parameters differs.
Object literal "Both" cannot implement all of those supertypes.
""", List.of("""
Sup1:{ .id[X:imm](x:Sup1):Sup1 }
Sup2:{ .id(x:Sup1):Sup1 }
A:{ .m[X](x:X): Sup1 -> Both:Sup1,Sup2{} }
"""));}
@Test void anAbstractMethodWithoutReturnTypeAndNoSupertype(){failWf("""
001| A:{ .m; }
   | ----^^---

While inspecting type declaration "A"
Missing return type for method ".m".
Add an explicit return type at the end of the signature.
Cannot infer signature of method ".m".
No supertype has a method named ".m" with 0 parameters.
""", List.of("""
A:{ .m; }
"""));}
@Test void anAbstractMethodWithAParameterWithoutReturnTypeAndNoSupertype(){failWf("""
001| A:{ .use(x: A); }
   | ----^^^^^^^^^^---

While inspecting type declaration "A"
Missing return type for method ".use(_)".
Add an explicit return type at the end of the signature.
Cannot infer signature of method ".use(_)".
No supertype has a method named ".use(_)" with 1 parameter.
""", List.of("""
A:{ .use(x: A); }
"""));}
@Test void anImmMethodDoesNotInheritFromAMutMethod(){failWf("""
002| B:A{ imm .m -> this }
   | -----^^^^^^^^^^^^^^--

While inspecting type declaration "B"
Missing return type for method "imm .m".
Cannot infer signature of method "imm .m".
No supertype has a method named "imm .m" with 0 parameters.
Did you mean "mut .m" ?
""", List.of("""
A:{ mut .m: A }
B:A{ imm .m -> this }
"""));}
@Test void aMethodWithTheWrongNumberOfParametersSuggestsTheMethodOfTheSupertype(){failWf("""
004| U:{ .u: A -> O.match{ .some -> A; .empty -> A } }
   |                     --^^^^^^^^^^---------------

While inspecting object literal instance of "OM[_]"
Missing return type for method ".some".
Cannot infer signature of method ".some".
No supertype has a method named ".some" with 0 parameters.
Did you mean ".some(_)" ?
Other methods of the supertypes:
- ".empty"
""", List.of("""
A:{}
OM[R]:{ .some(a: A): R; .empty: R }
O:{ .match[R](m: OM[R]): R -> m.empty }
U:{ .u: A -> O.match{ .some -> A; .empty -> A } }
"""));}
@Test void aMisspelledMethodSuggestsTheMethodOfTheSupertype(){failWf("""
004| U:{ .u: A -> B.if{ .then -> A; .els -> A } }
   |                  --------------^^^^^^^^^--

While inspecting object literal instance of "IfM[_]"
Missing return type for method ".els".
Cannot infer signature of method ".els".
No supertype has a method named ".els" with 0 parameters.
Did you mean ".else" ?
Other methods of the supertypes:
- ".then"
""", List.of("""
A:{}
IfM[R]:{ .then: R; .else: R }
B:{ .if[R](m: IfM[R]): R -> m.then }
U:{ .u: A -> B.if{ .then -> A; .els -> A } }
"""));}
@Test void aMisspelledMethodSuggestsEachMethodOfTheSupertypeWithThatName(){failWf("""
004| U:{ .u: A -> B.if{ .then -> A; .els -> A } }
   |                  --------------^^^^^^^^^--

While inspecting object literal instance of "IfM[_]"
Missing return type for method ".els".
Cannot infer signature of method ".els".
No supertype has a method named ".els" with 0 parameters.
Did you mean one of the following?
- ".else(_)"
- "read .else"
Other methods of the supertypes:
- ".then"
""", List.of("""
A:{}
IfM[R]:{ .then: R; .else(r: R): R; read .else: R }
B:{ .if[R](m: IfM[R]): R -> m.then }
U:{ .u: A -> B.if{ .then -> A; .els -> A } }
"""));}
@Test void aMethodNameWithoutTheDotIsReadAsAParameterName(){failWf("""
003| West:Direction{ turn -> North }
   | ----------------^^^^^^^^^^^^^--

While inspecting type declaration "West"
Cannot infer signature and name for a method with 1 parameter.
No supertype of type declaration "West" has a method with 1 parameter.
"turn" is read as a parameter name: a method name starts with ".", as in ".turn".
""", List.of("""
Direction:{ .turn: Direction }
North:Direction{ .turn -> North }
West:Direction{ turn -> North }
"""));}
@Test void aMethodNameWithoutTheDotListsTheOtherMethodsOfTheSupertypes(){failWf("""
003| West:Direction{ turn -> North }
   | ----------------^^^^^^^^^^^^^--

While inspecting type declaration "West"
Cannot infer signature and name for a method with 1 parameter.
No supertype of type declaration "West" has a method with 1 parameter.
"turn" is read as a parameter name: a method name starts with ".", as in ".turn".
Other methods of the supertypes:
- ".back"
""", List.of("""
Direction:{ .turn: Direction; .back: Direction }
North:Direction{ .turn -> North; .back -> North }
West:Direction{ turn -> North }
"""));}
@Test void aLambdaWithTooManyParametersListsTheMethodsOfTheSupertype(){failWf("""
003| U:{ .u(f: F[A,A]): A -> A; .k: A -> this.u{ a, b -> a } }
   |                                           --^^^^^^^^^--

While inspecting object literal instance of "F[_,_]"
Cannot infer signature and name for a method with 2 parameters.
No supertype of object literal instance of "F[_,_]" has a method with 2 parameters.
Methods of the supertypes:
- "#(_)"
""", List.of("""
A:{}
F[X,R]:{ #(x: X): R }
U:{ .u(f: F[A,A]): A -> A; .k: A -> this.u{ a, b -> a } }
"""));}
@Test void aMethodWithInferredNameWhoseSupertypeMethodIsTakenSaysSo(){failWf("""
002| B:A{ .m(a) -> this; a -> this }
   | --------------------^^^^^^^^^--

While inspecting type declaration "B"
Cannot infer signature and name for a method with 1 parameter.
Each method with 1 parameter of the supertypes is already overridden by another method of type declaration "B".
Methods of the supertypes:
- ".m(_)"
""", List.of("""
A:{ .m(a: A): A }
B:A{ .m(a) -> this; a -> this }
"""));}
@Test void unnamedMethodImplementsTheOtherReceiverCapability(){ok(List.of("""
A:{ mut .m(a: A): A }
B:A{ imm .m(a: A): A -> this; a -> a }
"""));}
@Test void unnamedMethodAfterANamedMethodTakingEveryReceiverCapability(){failWf("""
002| B:A{ .m(a: A): A -> this; a -> this }
   | --------------------------^^^^^^^^^--

While inspecting type declaration "B"
Cannot infer signature and name for a method with 1 parameter.
Each method with 1 parameter of the supertypes is already overridden by another method of type declaration "B".
Methods of the supertypes:
- "mut .m(_)"
""", List.of("""
A:{ mut .m(a: A): A }
B:A{ .m(a: A): A -> this; a -> this }
"""));}
@Test void unnamedMethodAfterANamedAbstractMethod(){failWf("""
002| B:A{ .m(a: A): A; a -> this }
   | ------------------^^^^^^^^^--

While inspecting type declaration "B"
Cannot infer signature and name for a method with 1 parameter.
Each method with 1 parameter of the supertypes is already overridden by another method of type declaration "B".
Methods of the supertypes:
- ".m(_)"
""", List.of("""
A:{ .m(a: A): A }
B:A{ .m(a: A): A; a -> this }
"""));}
@Test void unnamedMethodImplementsTheMutOverloadOfAnImmLiteral(){ok(List.of("""
A:{ mut .m(a: A): A; imm .m(a: A): A }
C:{ .f: A -> A{ .m(a) -> a; b -> b } }
"""));}
}
