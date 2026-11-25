package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public final class ReceiverLiteralTest extends testUtils.FearlessTestBase{
  static void ok(String input){ typeOk(List.of(input)); }
  static void fail(String expected, String input){ typeFail(expected, List.of(input)); }
  static void failWf(String expected, String input){ failWf(expected, List.of(input)); }

@Test void ownOperatorMethodWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {*: X -> this.x}* }
""");}
@Test void ownMethodWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {.get: X -> this.x}.get }
""");}
@Test void ownMethodWithAReadGenericExpectedType(){ok("""
A[X:*]:{ .x: read X; #: read X -> {.get: read X -> this.x}.get }
""");}
@Test void ownMethodWithAReadImmGenericExpectedType(){ok("""
A[X:*]:{ .x: read/imm X; #: read/imm X -> {.get: read/imm X -> this.x}.get }
""");}
@Test void ownMethodWithAnIsoBoundGenericExpectedType(){ok("""
A[X:**]:{ .x: X; #: X -> {.get: X -> this.x}.get }
""");}
@Test void ownMethodWithAParameterAndAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {.get(y: X): X -> y}.get(this.x) }
""");}
@Test void ownGenericMethodWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {.get[Z:*](z: Z): Z -> z}.get(this.x) }
""");}
@Test void ownReadMethodWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {read .get: X -> this.x}.get }
""");}
@Test void ownMethodThroughTheSelfNameWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {'s .get: X -> this.x; .me: X -> s.get}.me }
""");}
@Test void ownMethodAtTheRootOfACallChainWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {.a: A[X] -> this; .b: X -> this.x}.a.x }
""");}
@Test void nestedReceiverLiteralsWithAGenericExpectedType(){ok("""
A[X:*]:{ .x: X; #: X -> {.get: X -> {.in: X -> this.x}.in}.get }
""");}
@Test void ownMethodAsAnArgumentWithANominalExpectedType(){ok("""
Q:{} B:{ .id[Y:*](y: Y): Y -> y; .m: Q -> this.id({.get: Q -> Q}.get) }
""");}
@Test void ownMethodAsAnArgumentWithAnExpectedTypeNoConstraintDecides(){ok("""
Q:{} B:{ .ign[Y:*](y: Y): Q -> Q; .m: Q -> this.ign({.get: Q -> Q}.get) }
""");}
@Test void ownMethodAsAnArgumentThroughAMethodGenericDecidedToAGenericType(){ok("""
A[X:*]:{ .x: X; .id[Y:*](y: Y): Y -> y; #: X -> this.id({.get: X -> this.x}.get) }
""");}
@Test void ownMethodCapturingAMutThisWithAMutGenericExpectedType(){fail("""
001| A[X:*]:{ mut .x: mut X; mut #: mut X -> {.get: mut X -> this.x}.get }
   |                         -----------------~~~~~~~~~~~~~~~^^^^~~-----

While inspecting parameter "this" > method "{...}.get" (line 1) > method "A[_]#" (line 1)
Parameter "this" has type "mut A[X]".
Parameter "this" can observe mutation;
thus it cannot be captured in the "imm" object literal "{...}" (line 1).
Capture an immutable copy instead, or move this use outside the object literal.
""", """
A[X:*]:{ mut .x: mut X; mut #: mut X -> {.get: mut X -> this.x}.get }
""");}
@Test void emptyLiteralWithAForeignSealedExpectedTypeIsThatType(){ok("""
A:{ .m: base.Nat -> {} + base.Zero }
""");}
@Test void foreignSealedTypeByName(){ok("""
A:{ .m: base.Nat -> base.Nat + base.Zero }
""");}
@Test void foreignSealedTypeByNameWithEmptyCurlyBraces(){ok("""
A:{ .m: base.Nat -> base.Nat{} + base.Zero }
""");}
@Test void emptyLiteralWithASealedExpectedTypeOfTheSamePackage(){ok("""
S:base.Sealed{ .foo: S -> this } A:{ .m: S -> {}.foo }
""");}
@Test void sealedTypeOfTheSamePackageByName(){ok("""
S:base.Sealed{ .foo: S -> this } A:{ .m: S -> S.foo }
""");}
@Test void emptyLiteralWithAnExpectedTypeWithNoAbstractMethods(){ok("""
S:{ .foo: S -> this } A:{ .m: S -> {}.foo }
""");}
@Test void literalWithMethodsAndAForeignSealedExpectedTypeIsItsOwnType(){fail("""
001| A:{ .m: base.Nat -> {.k: base.Nat -> base.Zero} + base.Zero }
   |     ----------------~~~~~~~~~~~~~~~~~~~~~~~~~~~~^~~~~~~~~~~

While inspecting method "A.m" (line 1)
This call to method "+(_)" cannot typecheck.
Method "+(_)" is not declared on "{...}".

Available methods on "{...}":
-       .k: base.Nat
""", """
A:{ .m: base.Nat -> {.k: base.Nat -> base.Zero} + base.Zero }
""");}
@Test void emptyLiteralWithAForeignSealedExpectedTypeWithoutTheMethod(){fail("""
001| A:{ .m: base.Void -> {}.foo }
   |     -----------------~~^^^^

While inspecting method "A.m" (line 1)
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on type "base.Void".
Type "base.Void" does not have any methods.
""", """
A:{ .m: base.Void -> {}.foo }
""");}
@Test void emptyLiteralWithAForeignSealedExpectedTypeWithAbstractMethods(){fail("""
001| A:{ .m: base.Bool -> {}.not }
   |     -----------------^^----

While inspecting object literal instance of "base.Bool" > method "A.m" (line 1)
This object literal is missing a required method.
Missing: the "imm" method ".and(_)".
Required by: "base.Bool".
Sealed types can only be implemented in their own package.
Type "base.Bool" is in package "base".
""", """
A:{ .m: base.Bool -> {}.not }
""");}
@Test void foreignSealedTypeWithAbstractMethodsByName(){fail("""
001| A:{ .m: base.Bool -> base.Bool.not }
   |     -----------------^^^^^^^^^----

While inspecting object literal instance of "base.Bool" > method "A.m" (line 1)
This object literal is missing a required method.
Missing: the "imm" method ".and(_)".
Required by: "base.Bool".
Sealed types can only be implemented in their own package.
Type "base.Bool" is in package "base".
""", """
A:{ .m: base.Bool -> base.Bool.not }
""");}
@Test void emptyLiteralWithAnExpectedTypeWithAnAbstractMethod(){fail("""
001| S:{ .foo: S } A:{ .m: S -> {}.foo }
   |                   ---------^^----

While inspecting object literal instance of "S" > method "A.m" (line 1)
This object literal is missing a required method.
Missing: the "imm" method ".foo".
Required by: "S".
Add an implementation for ".foo" inside the object literal.
""", """
S:{ .foo: S } A:{ .m: S -> {}.foo }
""");}
@Test void emptyLiteralWithAGenericForeignSealedExpectedType(){failWf("""
001| A:{ .m: base.Block[base.Nat] -> {}.done }
   |                                 ^^

While inspecting object literal instance of "base.Block[_]"
Type inference concluded that this object literal implements "base.Block[?]",
but it could not infer generic type argument 1 for generic type parameter "R" of "base.Block[_]".
""", """
A:{ .m: base.Block[base.Nat] -> {}.done }
""");}
@Test void undeclaredOperatorMethodWithAGenericExpectedType(){fail("""
001| A[X:*]:{ #: X -> {.foo: A[X] -> this}* }
   |          --------~~~~~~~~~~~~~~~~~~~~^

While inspecting method "A[_]#" (line 1)
This call to method "*" cannot typecheck.
Method "*" is not declared on "{...}".

Available methods on "{...}":
-       .foo: A[X]
""", """
A[X:*]:{ #: X -> {.foo: A[X] -> this}* }
""");}
@Test void undeclaredMethodWithAGenericExpectedType(){fail("""
001| A[X:*]:{ .x: X; #: X -> {.get: X -> this.x}.other }
   |                 --------~~~~~~~~~~~~~~~~~~~^^^^^^

While inspecting method "A[_]#" (line 1)
This call to method ".other" cannot typecheck.
Method ".other" is not declared on "{...}".

Available methods on "{...}":
-       .get: X
""", """
A[X:*]:{ .x: X; #: X -> {.get: X -> this.x}.other }
""");}
@Test void undeclaredMethodOnAnEmptyLiteralWithAGenericExpectedType(){fail("""
001| A[X:*]:{ #: X -> {}.foo }
   |          --------~~^^^^

While inspecting method "A[_]#" (line 1)
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on "{...}".
Object literal "{...}" does not have any methods.
""", """
A[X:*]:{ #: X -> {}.foo }
""");}
@Test void ownMethodReturningAnotherTypeThanTheGenericExpectedType(){fail("""
001| A[X:*]:{ #: X -> {.get: A[X] -> this}.get }
   |          --------^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".get" > method "A[_]#" (line 1)
The body of method "#" of type declaration "A[_]" is an expression returning "A[X]".
Method call "{...}.get" has type "A[X]" instead of a subtype of "X".
""", """
A[X:*]:{ #: X -> {.get: A[X] -> this}.get }
""");}
@Test void ownMethodCapturingAMutableParameterOfAMethodGenericType(){fail("""
001| B:{ .m[Y:*](y: Y): Y -> {.get: Y -> y}.get }
   |     ---------------------~~~~~~~~~~~^-----

While inspecting parameter "y" > method "{...}.get" (line 1) > method "B.m(_)" (line 1)
Parameter "y" has type "Y".
Parameter "y" can observe mutation;
thus it cannot be captured in the "imm" object literal "{...}" (line 1).
Capture an immutable copy instead, or move this use outside the object literal.
""", """
B:{ .m[Y:*](y: Y): Y -> {.get: Y -> y}.get }
""");}
@Test void ownMethodAsAnArgumentForAParameterOfAMethodGenericType(){fail("""
001| B:{ .m[Y:*](y: Y): Y -> this.m({.get: Y -> y}.get) }
   |     ----------------------------~~~~~~~~~~~^------

While inspecting parameter "y" > method "{...}.get" (line 1) > method "B.m(_)" (line 1)
Parameter "y" has type "Y".
Parameter "y" can observe mutation;
thus it cannot be captured in the "imm" object literal "{...}" (line 1).
Capture an immutable copy instead, or move this use outside the object literal.
""", """
B:{ .m[Y:*](y: Y): Y -> this.m({.get: Y -> y}.get) }
""");}
@Test void ownMethodWithoutReturnTypeWithAGenericExpectedType(){failWf("""
001| A[X:*]:{ .x: X; #: X -> {.get -> this.x}.get }
   |                         -^^^^^^^^^^^^^^-

While inspecting object literal "{...}"
Missing return type for method ".get".
Add an explicit return type before "->".
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".get".
No supertype has a method ".get".
""", """
A[X:*]:{ .x: X; #: X -> {.get -> this.x}.get }
""");}
@Test void methodWithoutReturnTypeAndAnUndeclaredOperatorWithAGenericExpectedType(){failWf("""
001| A[X:*]:{ #: X -> {.foo -> this}* }
   |                  -^^^^^^^^^^^^-

While inspecting object literal "{...}"
Missing return type for method ".foo".
Add an explicit return type before "->".
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".foo".
No supertype has a method ".foo".
""", """
A[X:*]:{ #: X -> {.foo -> this}* }
""");}
}
