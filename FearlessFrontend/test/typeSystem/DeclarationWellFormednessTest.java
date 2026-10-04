package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class DeclarationWellFormednessTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failWf(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input);
  }
  static void failParse(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 2 UnexpectedToken", input);
  }
  static void failsWithACompileError(List<String> input){ typeFailRaw("[###]", input); }

@Test void noExplicitThisSelfName(){failParse("""
001| A:{ .m1: A -> {'this} }
   |     ----------~~^^^^~

While inspecting object literal > method body > method declaration > type declaration body > type declaration > full file
Name "this" already in scope.
""",List.of("""
A:{ .m1: A -> {'this} }
"""));}
@Test void noExplicitThisMethArg(){failParse("""
001| A:{ .foo(this: A): A }
   |     -----^^^^~~~----

While inspecting method parameters declaration > method declaration > type declaration body > type declaration > full file
Name "this" already in scope.
""",List.of("""
A:{ .foo(this: A): A }
"""));}
@Test void disjointArgList(){failParse("""
001| A:{ .foo(a: A, a: A): A }
   | --~~^^^^^^^^^^^^^^^^^^^~~

While inspecting method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple parameters with the same name
Parameter "a" is repeated
""",List.of("""
A:{ .foo(a: A, a: A): A }
"""));}
@Test void disjointMethGens(){failParse("""
001| A:{ .foo[T:*,T:*](a: T, b: T): A }
   | --~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^~~

While inspecting method declaration > type declaration body > type declaration > full file
A method signature cannot declare multiple generic type parameters with the same name
Generic type parameter "T" is repeated
""",List.of("""
A:{ .foo[T:*,T:*](a: T, b: T): A }
"""));}
@Test void disjointDecGens(){failParse("""
001| A[T:*,T:*]:{ .foo(a: T, b: T): A }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration > full file
A method signature cannot declare multiple generic type parameters with the same name
Generic type parameter "T" is repeated
""",List.of("""
A[T:*,T:*]:{ .foo(a: T, b: T): A }
"""));}
@Test void noShadowingMeths(){failWf("""
001| A:{ .a: A; .a: A }
   | --~~~~~~~~~^^^^^~~

While inspecting type declaration body > type declaration > full file
Method ".a" redeclared.
A method with the same name, arity and reference capability is already present.
""",List.of("""
A:{ .a: A; .a: A }
"""));}
@Test void useUndefinedX(){failParse("""
001| A[X:*]:{ .foo(x: X): X -> B{ x }.argh }
002| B:{ read .argh: read/imm X }
   |   --~~~~~~~~~~~~~~~~~~~~~^--

While inspecting method declaration > type declaration body > type declaration > full file
Generic type "X" is not in scope.
No generic parameters are declared here.
""",List.of("""
A[X:*]:{ .foo(x: X): X -> B{ x }.argh }
B:{ read .argh: read/imm X }
"""));}
@Test void useUndefinedIdent(){failParse("""
001| A[X:*]:{ .foo(x: X): X -> this.foo(b) }
   |          -----------------~~~~~~~~~^~

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Name "b" is not in scope.
In scope: "this", "x".
""",List.of("""
A[X:*]:{ .foo(x: X): X -> this.foo(b) }
"""));}
@Test void noShadowingSelfName(){failParse("""
001| Foo:{ .m1: Foo -> Foo{ 'unique
002|   .m1 -> {'unique}
   |   -------~~^^^^^^~
003|   } }

While inspecting object literal > method body > method declaration > typed literal > method body > method declaration > type declaration body > type declaration > full file
Name "unique" already in scope.
""",List.of("""
Foo:{ .m1: Foo -> Foo{ 'unique
  .m1 -> {'unique}
  } }
"""));}
@Test void noTopLevelSelfName(){failWf("""
001| A:{ 'self
   |      ^^^^
002|   .me: A -> self;
003|   }

While inspecting type declaration body > type declaration > full file
Self name "self" is invalid in a top level type.
Top level types self names can only be "this".
""",List.of("""
A:{ 'self
  .me: A -> self;
  }
"""));}
@Test void lambdaSelfNameOk(){ok(List.of("""
A:{ .me: A -> {'self} }
"""));}
@Test void noShadowingOk(){ok(List.of("""
A:{ .m1(a: A): A -> {.m1(b) -> a} }
"""));}
@Test void noShadowingParam(){failParse("""
001| A:{ .m1(a: A): A -> {.m1(a) -> a} }
   |                      ~~~~^~-----

While inspecting method parameters declaration > method signature > method declaration > object literal > method body > method declaration > type declaration body > type declaration > full file
Name "a" already in scope.
""",List.of("""
A:{ .m1(a: A): A -> {.m1(a) -> a} }
"""));}
@Test void lambdaImplementingItself(){failWf("""
001| A:A{}
   |   ^^

While inspecting type declarations
Circular implementation relation found involving "A".
""",List.of("""
A:A{}
"""));}
@Test void noMutHLambdaCreation(){failParse("""
001| A:{ #: mutH A -> mutH A }
   |     -------------^^^^~~

While inspecting method body > method declaration > type declaration body > type declaration > full file
Capability mutH used.
Capabilities readH and mutH are not allowed on object literals.
Use one of read, mut, imm, iso.
""",List.of("""
A:{ #: mutH A -> mutH A }
"""));}
@Test void noReadHLambdaCreation(){failParse("""
001| A:{ #: readH A -> readH A }
   |     --------------^^^^^~~

While inspecting method body > method declaration > type declaration body > type declaration > full file
Capability readH used.
Capabilities readH and mutH are not allowed on object literals.
Use one of read, mut, imm, iso.
""",List.of("""
A:{ #: readH A -> readH A }
"""));}
@Test void noReadImmLambdaCreation(){failParse("""
001| A:{ #: A -> this.eat(read/imm A); .eat(a: A): A -> a }
   |             ---------^^^^^^^^~~-

While inspecting arguments list > method body > method declaration > type declaration body > type declaration > full file
Missing expression.
Found instead: "read/imm".
Expected one of: "name", "type name", "(", "{".
""",List.of("""
A:{ #: A -> this.eat(read/imm A); .eat(a: A): A -> a }
"""));}
@Test void noReadImmOnNominalType(){failParse("""
001| A:{ #: read/imm A -> this# }
   |     ~~~~~~~~~~~~^---------

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Generic type "A" is not in scope.
No generic parameters are declared here.
""",List.of("""
A:{ #: read/imm A -> this# }
"""));}
@Test void abstractMethodOnlyAtTopLevel(){failWf("""
001| A:{ .foo: A }
002| B:A{}
003| Bs:{ #: B -> B{ .foo: A } }
   |              -~~^^^^^^^~~

While inspecting method declaration > typed literal > method body > method declaration > type declaration body > type declaration > full file
Abstract method declaration for ".foo".
Only top level methods can be abstract.
""",List.of("""
A:{ .foo: A }
B:A{}
Bs:{ #: B -> B{ .foo: A } }
"""));}
@Test void validPosInt(){ok(List.of("""
A:{ #: base.Int -> +5 }
"""));}
@Test void validNegInt(){ok(List.of("""
A:{ #: base.Int -> -5 }
"""));}
@Test void validNat(){ok(List.of("""
A:{ #: base.Nat -> 5 }
"""));}
@Test void validFloat(){ok(List.of("""
A:{ #: base.Float -> +5.5 }
"""));}
@Test void validString(){ok(List.of("""
A:{ #: base.Str -> "Hello" }
"""));}
@Test void duplicatedDeclarationTopLevelAndInline(){failWf("""
002| B:{ #: A -> A:{} }
   |             ^^

While inspecting a type name
Duplicate type declaration for "A".
""",List.of("""
A:{}
B:{ #: A -> A:{} }
"""));}
@Test void duplicatedInlineDeclarations(){failWf("""
002| C:{ #: A -> A:{} }
   |             ^^

While inspecting a type name
Duplicate type declaration for "A".
""",List.of("""
B:{ #: A -> A:{} }
C:{ #: A -> A:{} }
"""));}
@Test void inlineDeclarationCalledTwice(){ok(List.of("""
B:{ #: A -> A:{} }
C1:{ #: A -> B# }
C2:{ #: A -> B# }
"""));}
@Test void inlineDeclarationResultUsedTwice(){ok(List.of("""
B:{ #: A -> A:{} }
C1:{ #(b: B): A -> C2#(b#, b#) }
C2:{ #(a1: A, a2: A): A -> a1 }
"""));}
@Test void allowTopLevelDeclInsideMethod(){ok(List.of("""
Str:{} Bob:Str{}
Nat:{} TwentyFour:Nat{}
FPerson:{ #(name: Str, age: Nat): Person -> Person:{
  .name: Str -> name;
  .age: Nat -> age;
  }}
Ex:{
  .create: Person -> FPerson#(Bob, TwentyFour);
  .name(p: Person): Str -> p.name;
  }
"""));}
@Test void cannotImplementDeclarationDeclaredInsideMethod(){fail("""
006| Bad:Person{}
   | ^^^^^^^^^^^^

While inspecting type declaration "Bad"
The type "Person" is declared inside a method body.
A type declared inside a method can capture any parameter name in scope,
so it cannot be extended or instantiated.
Hint: if it captures nothing, declare it implementing "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
Bad:Person{}
""",List.of("""
Str:{} Nat:{}
FPerson:{ #(name: Str, age: Nat): Person -> Person:{
  .name: Str -> name;
  .age: Nat -> age;
  }}
Bad:Person{}
"""));}
@Test void noFreeGensInInlineDeclaration(){failParse("""
002| FPerson:{ #[N:*](name: Str, age: N): Person -> Person:{
003|   .name: Str -> name;
004|   .age: N -> age;
   |   ~~~~~~^-------
005|   }}

While inspecting method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type "N" is not in scope inside the type declaration "Person".
A type declaration only sees the generic types it declares itself; here "Person" declares none.
Hint: funnel "N" into "Person" by writing "Person[N:..]", restating the bounds of "N".
""",List.of("""
Str:{}
FPerson:{ #[N:*](name: Str, age: N): Person -> Person:{
  .name: Str -> name;
  .age: N -> age;
  }}
"""));}
@Test void genericFunnelling(){ok(List.of("""
Str:{}
FPerson:{ #[N:imm](name: Str, age: N): Person[N] -> Person[N:imm]:{
  .name: Str -> name;
  .age: N -> age;
  }}
"""));}
@Test void genericFunnellingFresh(){ok(List.of("""
Str:{}
Person[N:imm]:{ .name: Str; .age: N }
FPerson:{ #[N:imm](name: Str, age: N): Person[N] -> {
  .name -> name;
  .age -> age;
  }}
"""));}
@Test void genericFunnellingFreshNoBody(){ok(List.of("""
Str:{}
Person[N:imm]:{ .name: Str; .age: N }
Person2[N:imm]:Person[N]{ .name -> this.name; .age -> this.age }
FPerson:{ #[N:imm](name: Str, age: N): Person[N] -> Person2[N] }
"""));}
@Test void nonExistentImplInline(){failWf("""
002| BreakOuter:{ #: BreakInner -> BreakInner: A[imm Break]{} }
   |                                                 ^^^^^^

While inspecting a type name
Type "Break" is not declared in package "p" and is not made visible via "use".
In scope: "A", "BreakInner", "BreakOuter".
""",List.of("""
A[X:mut]:{}
BreakOuter:{ #: BreakInner -> BreakInner: A[imm Break]{} }
"""));}
@Test void inlineDeclarationImplementingAnEnclosingGenericWithoutFunnelling(){failParse("""
001| A[X:mut]:{}
002| BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[Z]{} }
   |                                      ------------~~^~--

While inspecting generic types > super types declaration > method body > method declaration > type declaration body > type declaration > full file
Generic type "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic types it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""",List.of("""
A[X:mut]:{}
BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[Z]{} }
"""));}
@Test void inlineDeclarationImplementingAnEnclosingGenericWithFunnelling(){ok(List.of("""
A[X:mut]:{}
BreakOuter[Z:mut]:{ #: BreakInner[Z] -> BreakInner[Z:mut]: A[Z]{} }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericWithoutFunnelling(){failParse("""
001| A[X:*]:{}
002| BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A[Z] -> A[Z] } }
   |                                                 ~~~~~~^~--------

While inspecting generic types > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic types it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""",List.of("""
A[X:*]:{}
BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A[Z] -> A[Z] } }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericWithFunnelling(){ok(List.of("""
A[X:*]:{}
BreakOuter[Z:*]:{ #: BreakInner[Z] -> BreakInner[Z:*]:{ .z: A[Z] -> A[Z] } }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericWithCapabilityWithoutFunnelling(){failParse("""
001| A[X:mut]:{}
002| BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[mut Z]{} }
   |                                                  --~~~~^-

While inspecting generic types > super types declaration > method body > method declaration > type declaration body > type declaration > full file
Generic type "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic types it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""",List.of("""
A[X:mut]:{}
BreakOuter[Z:mut]:{ #: BreakInner -> BreakInner: A[mut Z]{} }
"""));}
@Test void inlineDeclarationPartiallyFunnelled(){failParse("""
001| A[X:*]:{}
002| BreakOuter[Y:*,Z:*]:{ #: BreakInner[Y] -> BreakInner[Y:*]:{ .z: A[Z] -> A[Z] } }
   |                                                             ~~~~~~^~--------

While inspecting generic types > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic types it declares itself; here "BreakInner" declares "Y".
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Y:..,Z:..]", restating the bounds of "Z".
""",List.of("""
A[X:*]:{}
BreakOuter[Y:*,Z:*]:{ #: BreakInner[Y] -> BreakInner[Y:*]:{ .z: A[Z] -> A[Z] } }
"""));}
@Test void inlineDeclarationCannotRedeclareAHiddenGeneric(){failParse("""
001| A[X:*]:{}
002| BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z[Z:*](z: Z): Z -> z } }
   |                                                 ---^~~----------

While inspecting generic bounds declaration > method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Name "Z" already in scope.
""",List.of("""
A[X:*]:{}
BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z[Z:*](z: Z): Z -> z } }
"""));}
@Test void inlineDeclarationInsideInlineDeclarationCannotFunnelAHiddenGeneric(){failParse("""
001| A:{}
002| BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A -> Inner2[Z:*]: A{} } }
   |                                                          -------^~~------

While inspecting generic bounds declaration > method body > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic types it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""",List.of("""
A:{}
BreakOuter[Z:*]:{ #: BreakInner -> BreakInner:{ .z: A -> Inner2[Z:*]: A{} } }
"""));}
@Test void inlineDeclarationUsingAnEnclosingGenericAsReadImmWithoutFunnelling(){failParse("""
001| A:{}
002| BreakOuter[Z:*]:{ #(z: Z): BreakInner -> BreakInner:{ .z: read/imm Z -> z } }
   |                                                       ~~~~~~~~~~~~~^-----

While inspecting method signature > method declaration > type declaration body > method body > method declaration > type declaration body > type declaration > full file
Generic type "Z" is not in scope inside the type declaration "BreakInner".
A type declaration only sees the generic types it declares itself; here "BreakInner" declares none.
Hint: funnel "Z" into "BreakInner" by writing "BreakInner[Z:..]", restating the bounds of "Z".
""",List.of("""
A:{}
BreakOuter[Z:*]:{ #(z: Z): BreakInner -> BreakInner:{ .z: read/imm Z -> z } }
"""));}
@Test void mustImplementMethodsInInlineDecOk(){ok(List.of("""
A:{ .foo: A }
Bs:{ #: B -> B: A{'b .foo -> b } }
"""));}
@Test void mustImplementMethodsInInlineDecFail(){fail("""
002| Bs:{ #: B -> B: A{} }
   |      --------^^^^^^

While inspecting object literal "iso B" > "#" line 2
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B:A{}
""",List.of("""
A:{ .foo: A }
Bs:{ #: B -> B: A{} }
"""));}
@Test void mustImplementMethodsInLambdaOk(){ok(List.of("""
A:{ .foo: A }
B:A{}
Bs:{ #: B -> B{'b .foo -> b } }
"""));}
@Test void mustImplementMethodsInLambdaFail(){fail("""
003| Bs:{ #: B -> B{} }
   |      --------^^-

While inspecting object literal instance of "iso B" > "#" line 3
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B
""",List.of("""
A:{ .foo: A }
B:A{}
Bs:{ #: B -> B{} }
"""));}
@Test void sealedOutsidePkg(){failWf("""
001| C:base.Void{}
   | ^^^^^^^^^^^^^

While inspecting type declaration "C"
Type declaration "C" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type declaration "C" is defined in package "p".
Type "Void" is defined in package "base".
""",List.of("""
C:base.Void{}
"""));}
@Test void sealedOutsidePkgInline(){failWf("""
001| Test:{ #: C -> C: base.Void{} }
   |                ^^^^^^^^^^^^^^

While inspecting object literal "C"
Object literal "C" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal "C" is defined in package "p".
Type "Void" is defined in package "base".
""",List.of("""
Test:{ #: C -> C: base.Void{} }
"""));}
@Test void sealedOutsidePkgMultiImpl(){failWf("""
002| Test:{ #: C -> C: base.Void,A{} }
   |                ^^^^^^^^^^^^^^^^

While inspecting object literal "C"
Object literal "C" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal "C" is defined in package "p".
Type "Void" is defined in package "base".
""",List.of("""
A:{}
Test:{ #: C -> C: base.Void,A{} }
"""));}
@Test void sealedWithinPkg(){ok(List.of("""
Sealed:{}
A:Sealed{}
B:A{}
"""));}
@Test void sealedOutsidePkgUsedThroughAConstructor(){ok(List.of("""
C:{ .foo: base.Void -> base.Void }
"""));}
@Test void allowPrivateLambdaUsageWithinPkg(){ok(List.of("""
_RootCap:{}
Good:{ .ok: mut _RootCap -> {} }
"""));}
@Test void noPrivateNameFromAnotherPkg(){failParse("""
001| A:{ #: base._RootCap -> {} }
   |     ~~~^^^^^^^^^^^^^------

While inspecting method signature > method declaration > type declaration body > type declaration > full file
Code is attempting to use private name "_RootCap" from package "base".
Type names starting with "_" can only be used in their own package, and only by their simple name.
""",List.of("""
A:{ #: base._RootCap -> {} }
"""));}
@Test void mutTypeWithGenericArgument(){ok(List.of("""
A[X:*]:{ .no: mut A[X] }
"""));}
@Test void readTypeNestedInReadType(){ok(List.of("""
A[X:*]:{ .no: read A[read A[X]] }
"""));}
@Test void supertypeWithAndWithoutDefaultImm(){failWf("""
003| B:A[Foo],A[imm Foo]{}
   | ^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Duplicated supertype in type declaration: "A[Foo]" and "A[imm Foo]" denote the same type.
Remove one of them.
""",List.of("""
Foo:{}
A[X:*]:{}
B:A[Foo],A[imm Foo]{}
"""));}
@Test void supertypeTypeVariableWithAndWithoutRedundantRc(){failWf("""
002| A[Y:imm]:Foo[Y],Foo[imm Y]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Duplicated supertype in type declaration: "Foo[Y]" and "Foo[imm Y]" denote the same type.
Remove one of them.
""",List.of("""
Foo[T:*]:{ .get: T }
A[Y:imm]:Foo[Y],Foo[imm Y]{}
"""));}
@Test void supertypeNestedTypeVariableWithAndWithoutRedundantRc(){failWf("""
[###]
Duplicated supertype in type declaration: "Foo[Box[read Y]]" and "Foo[Box[Y]]" denote the same type.
Remove one of them.
""",List.of("""
Box[T:*]:{}
Foo[T:*]:{}
A[Y:read]:Foo[Box[read Y]],Foo[Box[Y]]{}
"""));}
@Test void supertypeTypeVariableWithNonRedundantRcOk(){ok(List.of("""
Foo[T:*]:{}
A[Y:imm,mut]:Foo[Y],Foo[imm Y]{}
"""));}
@Test void supertypeSimpleAndQualified(){failWf("""
002| B:A,p.A{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Duplicated supertype in type declaration: "A" and "p.A" denote the same type.
Remove one of them.
""",List.of("""
A:{}
B:A,p.A{}
"""));}
@Test void supertypeUseAliasAndQualified(){failWf("""
002| B:CF,base.CaptureFree{}
   | ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Duplicated supertype in type declaration: "CF" and "base.CaptureFree" denote the same type.
Remove one of them.
""",List.of("""
use base.CaptureFree as CF;
B:CF,base.CaptureFree{}
"""));}
@Test void supertypeDifferentSpellingOfTypeArgument(){failWf("""
003| B:A[Foo],A[p.Foo]{}
   | ^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Duplicated supertype in type declaration: "A[Foo]" and "A[p.Foo]" denote the same type.
Remove one of them.
""",List.of("""
Foo:{}
A[X:*]:{}
B:A[Foo],A[p.Foo]{}
"""));}
@Test void claimOpenWithExt(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"foo"]{}
"""));}
@Test void claimOpenWith(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon]{}
"""));}
@Test void claimShortcutExt(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,"fapp042"]{}
"""));}
@Test void claimShortcut(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon]{}
"""));}
@Test void claimAllFour(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"q"],base.OpenWith[Icon],base.Shortcut[Icon,"fapp001"],base.Shortcut[Icon]{}
"""));}
@Test void claimTwoExtensions(){ok(List.of("""
Icon:base.ImageFile{}
Icon2:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"q"],base.OpenWith[Icon2,"b"]{}
"""));}
@Test void claimInheritedAlongTwoPaths(){ok(List.of("""
Icon:base.ImageFile{}
B:base.Main,base.OpenWith[Icon,"q"],base.Shortcut[Icon]{}
C:base.Main,base.OpenWith[Icon,"q"],base.Shortcut[Icon]{}
D:B,C{}
"""));}
@Test void claimRepeatedAndInherited(){ok(List.of("""
Icon:base.ImageFile{}
B:base.Main,base.OpenWith[Icon,"q"]{}
C:B,base.OpenWith[Icon,"q"]{}
"""));}
@Test void claimMainInherited(){ok(List.of("""
Icon:base.ImageFile{}
M:base.Main{}
A:M,base.Shortcut[Icon,"fapp042"]{}
"""));}
@Test void claimFearFappFfile(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"fear"],base.Shortcut[Icon,"fapp123"],base.OpenWith[Icon,`ffile123`],base.OpenWith[Icon,"abcdefghij012345"]{}
"""));}
@Test void claimNotMain(){failWf("""
002| A:base.OpenWith[Icon,"q"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.OpenWith[_,_]".
Only a main can open files: type declaration "A" must also implement "base.Main", directly or through one of its supertypes.
""",List.of("""
Icon:base.ImageFile{}
A:base.OpenWith[Icon,"q"]{}
"""));}
@Test void claimNotMainInline(){failWf("""
002| Test:{ #: C -> C: base.Shortcut[Icon]{} }
   |                ^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "C"
Object literal "C" implements "base.Shortcut[_]".
Only a main can open files: object literal "C" must also implement "base.Main", directly or through one of its supertypes.
""",List.of("""
Icon:base.ImageFile{}
Test:{ #: C -> C: base.Shortcut[Icon]{} }
"""));}
@Test void claimNotMainAnonymous(){failWf("""
002| Test:{ #: base.Shortcut[Icon] -> { .foo: base.Void -> base.Void } }
   |                                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.Shortcut[_]"
Object literal instance of "base.Shortcut[_]" implements "base.Shortcut[_]".
Only a main can open files: object literal instance of "base.Shortcut[_]" must also implement "base.Main", directly or through one of its supertypes.
""",List.of("""
Icon:base.ImageFile{}
Test:{ #: base.Shortcut[Icon] -> { .foo: base.Void -> base.Void } }
"""));}
@Test void claimNotMainIntermediate(){failWf("""
002| A:base.OpenWith[Icon,"q"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.OpenWith[_,_]".
Only a main can open files: type declaration "A" must also implement "base.Main", directly or through one of its supertypes.
""",List.of("""
Icon:base.ImageFile{}
A:base.OpenWith[Icon,"q"]{}
M:base.Main,A{}
"""));}
@Test void claimIconTypeVariable(){failWf("""
001| A[X:imm]:base.Main,base.OpenWith[X,"q"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Type declaration "A[_]" implements `base.OpenWith[X,"q"]`.
The icon "X" is not a concrete type name.
An icon is a type name with no type variables and no generic arguments, like "IconsFoo".
""",List.of("""
A[X:imm]:base.Main,base.OpenWith[X,"q"]{}
"""));}
@Test void claimIconGeneric(){failWf("""
003| A:base.Main,base.Shortcut[Box[Icon]]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.Shortcut[Box[Icon]]".
The icon "Box[Icon]" is not a concrete type name.
An icon is a type name with no type variables and no generic arguments, like "IconsFoo".
""",List.of("""
Icon:base.ImageFile{}
Box[X:imm]:{}
A:base.Main,base.Shortcut[Box[Icon]]{}
"""));}
@Test void claimExtTypeVariable(){failWf("""
002| A[X:imm]:base.Main,base.OpenWith[Icon,X]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A[_]"
Type declaration "A[_]" implements "base.OpenWith[Icon,X]".
The extension "X" is not a string literal type.
An extension is written as a string literal type, like `"foo"` or "`foo`".
""",List.of("""
Icon:base.ImageFile{}
A[X:imm]:base.Main,base.OpenWith[Icon,X]{}
"""));}
@Test void claimExtNotStr(){failWf("""
002| A:base.Main,base.OpenWith[Icon,Icon]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.OpenWith[Icon,Icon]".
The extension "Icon" is not a string literal type.
An extension is written as a string literal type, like `"foo"` or "`foo`".
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,Icon]{}
"""));}
@Test void claimExtNat(){failWf("""
002| A:base.Main,base.Shortcut[Icon,42]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.Shortcut[Icon,42]".
The extension "42" is not a string literal type.
An extension is written as a string literal type, like `"foo"` or "`foo`".
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,42]{}
"""));}
@Test void claimExtUpper(){failWf("""
002| A:base.Main,base.OpenWith[Icon,"Txt"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[Icon,"Txt"]`.
"Txt" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; "fearless" is reserved.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"Txt"]{}
"""));}
@Test void claimExtDot(){failWf("""
002| A:base.Main,base.OpenWith[Icon,"tar.gz"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[Icon,"tar.gz"]`.
"tar.gz" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; "fearless" is reserved.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"tar.gz"]{}
"""));}
@Test void claimExtLeadingDot(){failWf("""
002| A:base.Main,base.OpenWith[Icon,".txt"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[Icon,".txt"]`.
".txt" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; "fearless" is reserved.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,".txt"]{}
"""));}
@Test void claimExtEmpty(){failWf("""
002| A:base.Main,base.OpenWith[Icon,""]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[Icon,""]`.
"" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; "fearless" is reserved.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,""]{}
"""));}
@Test void claimExtTooLong(){failWf("""
002| A:base.Main,base.OpenWith[Icon,"abcdefghij0123456"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[Icon,"abcd-3456"]`.
"abcdefghij0123456" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; "fearless" is reserved.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"abcdefghij0123456"]{}
"""));}
@Test void claimExtFearless(){failWf("""
002| A:base.Main,base.OpenWith[Icon,`fearless`]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.OpenWith[Icon,`fearless`]".
"fearless" is not a valid extension.
An extension is 1 to 16 characters, each a lowercase letter "a"-"z" or a digit "0"-"9", with no dot; "fearless" is reserved.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,`fearless`]{}
"""));}
@Test void claimExtTwice(){failWf("""
003| A:base.Main,base.Shortcut[Icon,"fapp042"],base.Shortcut[Icon2,"fapp042"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" claims the extension "fapp042" more than once:
both `base.Shortcut[Icon,"fapp042"]` and `base.Shortcut[Icon2,"fapp042"]` claim it.
A main can claim each extension at most once, across all its "base.OpenWith[_,_]" and "base.Shortcut[_,_]", since one extension has one icon.
""",List.of("""
Icon:base.ImageFile{}
Icon2:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,"fapp042"],base.Shortcut[Icon2,"fapp042"]{}
"""));}
@Test void claimExtTwiceDelimiters(){failWf("""
002| A:base.Main,base.OpenWith[Icon,"txt"],base.OpenWith[Icon,`txt`]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" claims the extension "txt" more than once:
both `base.OpenWith[Icon,"txt"]` and "base.OpenWith[Icon,`txt`]" claim it.
A main can claim each extension at most once, across all its "base.OpenWith[_,_]" and "base.Shortcut[_,_]", since one extension has one icon.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"txt"],base.OpenWith[Icon,`txt`]{}
"""));}
@Test void claimShortcutFapp(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,"fapp042"]{}
"""));}
@Test void claimShortcutBar(){failWf("""
002| A:base.Main,base.Shortcut[Icon,"bar"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.Shortcut[Icon,"bar"]`.
"bar" is not a shortcut extension: a shortcut file only starts its main, so it must not look like a document of another program or a file of the project.
A shortcut extension is "fapp" followed by three digits, like "fapp042"; or implement "base.Shortcut[_]" to let the Fearless manager choose one.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,"bar"]{}
"""));}
@Test void claimShortcutFfile(){failWf("""
002| A:base.Main,base.Shortcut[Icon,"ffile042"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.Shortcut[Icon,"ffile042"]`.
"ffile042" is not a shortcut extension: a shortcut file only starts its main, so it must not look like a document of another program or a file of the project.
A shortcut extension is "fapp" followed by three digits, like "fapp042"; or implement "base.Shortcut[_]" to let the Fearless manager choose one.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,"ffile042"]{}
"""));}
@Test void claimShortcutDoc(){failWf("""
002| A:base.Main,base.Shortcut[Icon,"doc"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.Shortcut[Icon,"doc"]`.
"doc" is not a shortcut extension: a shortcut file only starts its main, so it must not look like a document of another program or a file of the project.
A shortcut extension is "fapp" followed by three digits, like "fapp042"; or implement "base.Shortcut[_]" to let the Fearless manager choose one.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.Shortcut[Icon,"doc"]{}
"""));}
@Test void claimOpenWithFapp(){failWf("""
002| A:base.Main,base.OpenWith[Icon,"fapp042"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[Icon,"fapp042"]`.
"fapp042" is a shortcut extension: "fapp" followed by three digits names the shortcut files of the Fearless manager.
Use an extension of the form "ffile" followed by three digits, like "ffile042", or a system extension, like "htm"; or implement "base.OpenWith[_]" to let the Fearless manager choose one.
""",List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"fapp042"]{}
"""));}
@Test void claimOpenWithFfileAndSystem(){ok(List.of("""
Icon:base.ImageFile{}
A:base.Main,base.OpenWith[Icon,"ffile042"],base.OpenWith[Icon,"doc"],base.OpenWith[Icon,`htm`],base.OpenWith[Icon,"notes"],base.OpenWith[Icon,"fapp0420"]{}
"""));}
@Test void iconDeclaredInLaterLayer(){ok(List.of("""
A:base.Main,base.OpenWith[Icon,"q"]{}
Icon:Img{}
Img:base.ImageFile{}
"""));}
@Test void iconFromBase(){ok(List.of("""
A:base.Main,base.Shortcut[base.IconsConflict],base.OpenWith[base.IconsConflict,"q"]{}
"""));}
@Test void iconInlineMain(){ok(List.of("""
Icon:base.ImageFile{}
Test:{ #: C -> C: base.Main,base.Shortcut[Icon]{'c .main -> c.main } }
"""));}
@Test void iconInlineDeclared(){ok(List.of("""
A:base.Main,base.OpenWith[C,"q"]{}
Test:{ #: C -> C: base.ImageFile{} }
"""));}
@Test void iconStr(){failWf("""
001| A:base.Main,base.OpenWith[base.Str,"q"]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements `base.OpenWith[base.Str,"q"]`.
The icon "base.Str" is not an image file.
An icon is the type generated for an image file, like "IconsFoo" for "_pkg/icons/foo.png", or "base.IconsConflict".
""",List.of("""
A:base.Main,base.OpenWith[base.Str,"q"]{}
"""));}
@Test void iconImageFileItself(){failWf("""
001| A:base.Main,base.Shortcut[base.ImageFile]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.Shortcut[base.ImageFile]".
The icon "base.ImageFile" is not an image file.
An icon is the type generated for an image file, like "IconsFoo" for "_pkg/icons/foo.png", or "base.IconsConflict".
""",List.of("""
A:base.Main,base.Shortcut[base.ImageFile]{}
"""));}
@Test void iconPlainDeclaration(){failWf("""
003| A:base.Main,base.Shortcut[Data]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.Shortcut[Data]".
The icon "Data" is not an image file.
An icon is the type generated for an image file, like "IconsFoo" for "_pkg/icons/foo.png", or "base.IconsConflict".
""",List.of("""
Data:Mid{}
Mid:{}
A:base.Main,base.Shortcut[Data]{}
"""));}
@Test void iconInheritedClaim(){failWf("""
003| A:base.Main,base.Shortcut[Data]{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Type declaration "A" implements "base.Shortcut[Data]".
The icon "Data" is not an image file.
An icon is the type generated for an image file, like "IconsFoo" for "_pkg/icons/foo.png", or "base.IconsConflict".
""",List.of("""
Data:{}
B:A{}
A:base.Main,base.Shortcut[Data]{}
"""));}
@Test void iconNotImageInlineMain(){failWf("""
002| Test:{ #: C -> C: base.Main,base.OpenWith[Data,"q"]{} }
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "C"
Object literal "C" implements `base.OpenWith[Data,"q"]`.
The icon "Data" is not an image file.
An icon is the type generated for an image file, like "IconsFoo" for "_pkg/icons/foo.png", or "base.IconsConflict".
""",List.of("""
Data:{}
Test:{ #: C -> C: base.Main,base.OpenWith[Data,"q"]{} }
"""));}
}
