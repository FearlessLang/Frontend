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
   |   ^^^

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
}
