package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class SubTypingTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }

@Test void reflSub(){ok(List.of("""
A:{}
Sub:{ .m(x: A): A -> x }
"""));}
@Test void noDSub(){fail("""
002| Sub:{ .m(x: A): B -> x }
   |       ---------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "A".
Parameter "x" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
Sub:{.m(x:A):B->x}
""",List.of("""
A:{} B:{}
Sub:{ .m(x: A): B -> x }
"""));}
@Test void directSub(){ok(List.of("""
A:B{} B:{}
Sub:{ .m(x: A): B -> x }
"""));}
@Test void inverseDirectSub(){fail("""
002| Sub:{ .m(x: B): A -> x }
   |       ---------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "B".
Parameter "x" has type "B" instead of a subtype of "A".

See inferred typing context below for how type "A" was introduced: (compression indicated by `-`)
Sub:{.m(x:B):A->x}
""",List.of("""
A:B{} B:{}
Sub:{ .m(x: B): A -> x }
"""));}
@Test void immIsSubTypeOfRead(){ok(List.of("""
A:{}
Sub:{ .m(x: imm A): read A -> x }
"""));}
@Test void readIsNotSubTypeOfImm(){fail("""
002| Sub:{ .m(x: read A): imm A -> x }
   |       ------------------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "read A".
Parameter "x" has type "read A" instead of a subtype of "imm A".

See inferred typing context below for how type "A" was introduced: (compression indicated by `-`)
Sub:{.m(x:read A):A->x}
""",List.of("""
A:{}
Sub:{ .m(x: read A): imm A -> x }
"""));}
@Test void mutIsNotSubTypeOfImm(){fail("""
002| Sub:{ .m(x: mut A): imm A -> x }
   |       -----------------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "mut A".
Parameter "x" has type "mut A" instead of a subtype of "imm A".

See inferred typing context below for how type "A" was introduced: (compression indicated by `-`)
Sub:{.m(x:mut A):A->x}
""",List.of("""
A:{}
Sub:{ .m(x: mut A): imm A -> x }
"""));}
@Test void transitiveSub(){ok(List.of("""
A:{} B:A{} C:B{}
Sub:{ .m(x: C): A -> x }
"""));}
@Test void inverseTransitiveSub(){fail("""
002| Sub:{ .m(x: A): C -> x }
   |       ---------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "A".
Parameter "x" has type "A" instead of a subtype of "C".

See inferred typing context below for how type "C" was introduced: (compression indicated by `-`)
Sub:{.m(x:A):C->x}
""",List.of("""
A:{} B:A{} C:B{}
Sub:{ .m(x: A): C -> x }
"""));}
@Test void transitiveManyStepsSub(){ok(List.of("""
A:{} B:A{} C:F,B,G{} D:C{} E:D{} F:{} G:{}
Sub:{ .m(x: E): A -> x }
"""));}
@Test void inverseTransitiveManyStepsSub(){fail("""
002| Sub:{ .m(x: A): E -> x }
   |       ---------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "A".
Parameter "x" has type "A" instead of a subtype of "E".

See inferred typing context below for how type "E" was introduced: (compression indicated by `-`)
Sub:{.m(x:A):E->x}
""",List.of("""
A:{} B:A{} C:B{} D:C{} E:D{}
Sub:{ .m(x: A): E -> x }
"""));}
@Test void readHIsCommonSupertype(){ok(List.of("""
A:{}
Sub:{
  .fromImm(x: imm A): readH A -> x;
  .fromRead(x: read A): readH A -> x;
  .fromMut(x: mut A): readH A -> x;
  .fromIso(x: iso A): readH A -> x;
  .fromReadH(x: readH A): readH A -> x;
  .fromMutH(x: mutH A): readH A -> x;
  }
"""));}
@Test void isoIsCommonSubtype(){ok(List.of("""
A:{}
Sub:{
  .toImm(x: iso A): imm A -> x;
  .toRead(x: iso A): read A -> x;
  .toMut(x: iso A): mut A -> x;
  .toIso(x: iso A): iso A -> x;
  .toReadH(x: iso A): readH A -> x;
  .toMutH(x: iso A): mutH A -> x;
  }
"""));}
@Test void mutIsSubTypeOfMutHAndRead(){ok(List.of("""
A:{}
Sub:{ .toMutH(x: mut A): mutH A -> x; .toRead(x: mut A): read A -> x }
"""));}
@Test void mutHIsNotSubTypeOfRead(){fail("""
002| Sub:{ .m(x: mutH A): read A -> x }
   |       -------------------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "mutH A".
Parameter "x" has type "mutH A" instead of a subtype of "read A".

See inferred typing context below for how type "read A" was introduced: (compression indicated by `-`)
Sub:{.m(x:mutH A):read A->x}
""",List.of("""
A:{}
Sub:{ .m(x: mutH A): read A -> x }
"""));}
@Test void genericArgIsInvariantSubTypeOk(){ok(List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m(x: SortedList[Int]): List[Int] -> x }
"""));}
@Test void genericArgIsInvariantMutArg(){fail("""
004| Sub:{ .m(x: SortedList[Int]): List[mut Int] -> x }
   |       -----------------------------------------^

While inspecting parameter "x" > ".m(_)" line 4
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[Int]".
Parameter "x" has type "SortedList[Int]" instead of a subtype of "List[mut Int]".

See inferred typing context below for how type "List[mut Int]" was introduced: (compression indicated by `-`)
Sub:{.m(x:Sor-ist[Int]):List[mut Int]->x}
""",List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m(x: SortedList[Int]): List[mut Int] -> x }
"""));}
@Test void genericArgIsInvariantReadArg(){fail("""
004| Sub:{ .m(x: SortedList[Int]): List[read Int] -> x }
   |       ------------------------------------------^

While inspecting parameter "x" > ".m(_)" line 4
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[Int]".
Parameter "x" has type "SortedList[Int]" instead of a subtype of "List[read Int]".

See inferred typing context below for how type "List[read Int]" was introduced: (compression indicated by `-`)
Sub:{.m(x:Sor-ist[Int]):List[read Int]->x}
""",List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m(x: SortedList[Int]): List[read Int] -> x }
"""));}
@Test void genericArgIsInvariantReadReceiver(){fail("""
004| Sub:{ .m(x: SortedList[read Int]): List[Int] -> x }
   |       ------------------------------------------^

While inspecting parameter "x" > ".m(_)" line 4
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[read Int]".
Parameter "x" has type "SortedList[read Int]" instead of a subtype of "List[Int]".

See inferred typing context below for how type "List[Int]" was introduced: (compression indicated by `-`)
Sub:{.m(x:Sor-ist[read Int]):List[Int]->x}
""",List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m(x: SortedList[read Int]): List[Int] -> x }
"""));}
@Test void genericArgIsInvariantWithTypeVariable(){ok(List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m[X:*](x: SortedList[X]): List[X] -> x }
"""));}
@Test void typeVariableIsNotANominalType(){fail("""
004| Sub:{ .m[X:*](x: SortedList[X]): List[Int] -> x }
   |       ----------------------------------------^

While inspecting parameter "x" > ".m(_)" line 4
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[X]".
Parameter "x" has type "SortedList[X]" instead of a subtype of "List[Int]".

See inferred typing context below for how type "List[Int]" was introduced: (compression indicated by `-`)
Sub:{.m[X:*](x:Sor-ist[X]):List[Int]->x}
""",List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m[X:*](x: SortedList[X]): List[Int] -> x }
"""));}
@Test void nominalTypeIsNotATypeVariable(){fail("""
004| Sub:{ .m[X:*](x: SortedList[Int]): List[X] -> x }
   |       ----------------------------------------^

While inspecting parameter "x" > ".m(_)" line 4
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[Int]".
Parameter "x" has type "SortedList[Int]" instead of a subtype of "List[X]".

See inferred typing context below for how type "List[X]" was introduced: (compression indicated by `-`)
Sub:{.m[X:*](x:Sor-ist[Int]):List[X]->x}
""",List.of("""
Int:{}
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m[X:*](x: SortedList[Int]): List[X] -> x }
"""));}
@Test void genericArgSubTypingIsNotCovariant(){fail("""
006| Sub:{ .m(x: SortedList[ColouredPoint]): SortedList[Point] -> x }
   |       -------------------------------------------------------^

While inspecting parameter "x" > ".m(_)" line 6
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[ColouredPoint]".
Parameter "x" has type "SortedList[ColouredPoint]" instead of a subtype of "SortedList[Point]".

See inferred typing context below for how type "SortedList[Point]" was introduced: (compression indicated by `-`)
Sub:{.m(x:Sor-ist[Col-int]):Sor-ist[Point]->x}
""",List.of("""
Int:{}
Point:{ .x: Int; .y: Int }
ColouredPoint:Point{ .colour: Int }
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m(x: SortedList[ColouredPoint]): SortedList[Point] -> x }
"""));}
@Test void genericArgSubTypingIsNotContravariant(){fail("""
006| Sub:{ .m(x: SortedList[Point]): SortedList[ColouredPoint] -> x }
   |       -------------------------------------------------------^

While inspecting parameter "x" > ".m(_)" line 6
The body of method ".m(_)" of type declaration "Sub" is an expression returning "SortedList[Point]".
Parameter "x" has type "SortedList[Point]" instead of a subtype of "SortedList[ColouredPoint]".

See inferred typing context below for how type "SortedList[ColouredPoint]" was introduced: (compression indicated by `-`)
Sub:{.m(x:Sor-ist[Point]):Sor-ist[Col-int]->x}
""",List.of("""
Int:{}
Point:{ .x: Int; .y: Int }
ColouredPoint:Point{ .colour: Int }
List[T:*]:{ read .get: read/imm T }
SortedList[T:*]:List[T]{}
Sub:{ .m(x: SortedList[Point]): SortedList[ColouredPoint] -> x }
"""));}
@Test void typeVariableIsNotSubTypeOfANominalType(){fail("""
002| Sub:{ .m[X:*](x: X): read Foo -> x }
   |       ---------------------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "X".
Parameter "x" has type "X" instead of a subtype of "read Foo".

See inferred typing context below for how type "read Foo" was introduced: (compression indicated by `-`)
Sub:{.m[X:*](x:X):read Foo->x}
""",List.of("""
Foo:{}
Sub:{ .m[X:*](x: X): read Foo -> x }
"""));}
}
