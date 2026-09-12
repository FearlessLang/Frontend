package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class MethodCompositionTest extends testUtils.FearlessTestBase{
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
Invalid method signature overriding for "B.foo(_)".
The method ".foo(_)" accepts parameter 1 of type "B".
But "A.foo(_)" requires "A", which is not a subtype of "B".
It is instead a supertype: you are strengthening the parameter instead of weakening it.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:A{.foo(B):Int}
""",List.of("""
Str:{} Int:{}
A:{ .foo(a:A):Str }
B:A{ .foo(b:B):Int }
"""));}
@Test void ownMethodStrengthensParamOfBothSupers(){fail("""
001| A:B,C{ .foo(a:A):A }
   | -------^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature overriding for "A.foo(_)".
The method ".foo(_)" accepts parameter 1 of type "A".
But "B.foo(_)" requires "B", which is not a subtype of "A".
It is instead a supertype: you are strengthening the parameter instead of weakening it.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B,C{.foo(A):A}
""",List.of("""
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
Invalid method signature overriding for "A.m".
The method ".m" returns type "Str".
But "B.m" returns type "Int", which is not a supertype of "Str".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Str}
""",List.of("""
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
Return type disagreement for method "imm .m" with 0 parameters.
Different options are present in the implemented types: "B", "C".
Type declaration "A" must declare a method ".m" explicitly choosing the desired option.
""",List.of("""
A:B,C{}
B:{ .m: B }
C:{ .m: C }
"""));}
@Test void twoSupersDisagreeOnRtInherited(){failWf("""
003| AA:B,C{}
   | ^^^^^^^^

While inspecting type declaration "AA"
Return type disagreement for method "imm .m" with 0 parameters.
Different options are present in the implemented types: "B", "C".
Type declaration "AA" must declare a method ".m" explicitly choosing the desired option.
""",List.of("""
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
Invalid method signature overriding for "A.m".
The method ".m" returns type "D".
But "B.m" returns type "B", which is not a supertype of "D".
It is instead a subtype: you are weakening the result instead of strengthening it.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B,C,D,D{.m:D}
""",List.of("""
A:B,C,D{ .m: D }
B:D{ .m: B }
C:D{ .m: B }
D:{ .m: B }
"""));}
@Test void sameNameDifferentArities(){fail("""
002| A[X:*]:A[X,X]{ .m(b:A):A }
   | ---------------^^^^^^^^^--

While inspecting type declaration "A[_]"
Invalid method signature overriding for "A[_].m(_)".
The method ".m(_)" returns type "A".
But "A[_,_].m(_)" returns type "A[X,X]", which is not a supertype of "A".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A[X:*]:A[X,X]{.m(A):A}
""",List.of("""
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
Ambiguous implementation for method ".m" with 1 parameters.
Different options are present in the implemented types:
Candidates: "B", "C".
Type declaration "A" must declare a method ".m" explicitly implementing the desired behaviour.
""",List.of("""
Foo:{}
A:B,C{}
B:{ .m(b:Foo): Foo -> b }
C:{ .m(c:Foo): Foo -> c }
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
Return type disagreement for method "imm .kk" with 0 parameters.
Different options are present in the implemented types: "A", "List[A]".
Type declaration "A" must declare a method ".kk" explicitly choosing the desired option.
""",List.of("""
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
   |            ^^

While inspecting a type name
Type "X" is not declared in package "p" and is not made visible via "use".
In scope: "A", "B", "Foo".
""",List.of("""
Foo:{}
A:B{ .m(x: X): Foo }
B:{ .m[X:*](x: X): Foo }
"""));}
@Test void overrideDeclaresTooManyTypeParameters(){failWf("""
002| A:B{ .m[X:*,Y:*]: Foo }
   |      ^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method implementation for "A.m".
The method ".m" declares 2 type parameter(s), but supertypes declare 1.
Local declaration: "[X:imm,mut,read, Y:imm,mut,read]".
From supertypes: "[-:imm,mut,read]".
Change the local number of type parameters to 1, or adjust the supertypes.
""",List.of("""
Foo:{}
A:B{ .m[X:*,Y:*]: Foo }
B:{ .m[X:*]: Foo }
"""));}
@Test void overrideDeclaresNarrowerBounds(){failWf("""
002| A:B{ .m[X:imm]: Foo }
   |      ^^^^^^^^^^^^^^

While inspecting type declaration "A"
Invalid method implementation for "A.m".
The local declaration uses different capability bounds than the supertypes for type parameter 1 of ".m".
Local: "X:imm".
From supertypes: "-:imm,mut,read".
The parameter name may differ; only the position matters.
Change the local bounds to match the supertypes, or adjust the supertypes.
""",List.of("""
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
Invalid method signature overriding for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Break[A]}
""",List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{}
"""));}
@Test void refineRtGenericArgContravariant(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature overriding for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Break[B]}
""",List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{}
"""));}
@Test void refineRtGenericArgCovariantWithGetter(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature overriding for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Break[A]}
""",List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{ .b: X }
"""));}
@Test void refineRtGenericArgContravariantWithGetter(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature overriding for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Break[B]}
""",List.of("""
A:B{ .m: Break[B] }
B:{ .m: Break[A] }
Break[X:*]:{ .b: X }
"""));}
@Test void refineRtGenericArgCovariantRecursive(){fail("""
001| A:B{ .m: Break[A] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature overriding for "A.m".
The method ".m" returns type "Break[A]".
But "B.m" returns type "Break[B]", which is not a supertype of "Break[A]".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Break[A]}
""",List.of("""
A:B{ .m: Break[A] }
B:{ .m: Break[B] }
Break[X:*]:{ .b: Break[X] }
"""));}
@Test void refineRtGenericArgContravariantRecursive(){fail("""
001| A:B{ .m: Break[B] }
   | -----^^^^^^^^^^^^--

While inspecting type declaration "A"
Invalid method signature overriding for "A.m".
The method ".m" returns type "Break[B]".
But "B.m" returns type "Break[A]", which is not a supertype of "Break[B]".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
A:B{.m:Break[B]}
""",List.of("""
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
Type disagreement about argument 0 for method "imm .m(_)" with 1 parameters.
Different options are present in the implemented types: "base.Int", "base.Float".
Type declaration "D" must declare a method ".m(_)" explicitly choosing the desired option.
""",List.of("""
A[X:*]:{ .m(x:X):X->x }
B:A[base.Int]{}
C:A[base.Float]{}
D:B,C{}
"""));}
}
