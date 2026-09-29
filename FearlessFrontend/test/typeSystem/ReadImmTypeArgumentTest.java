package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class ReadImmTypeArgumentTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }

@Test void typeArgumentReadImmXEqualsReadXWhenBoundHasOnlyMut(){ok(List.of("""
Box[T:*]:{}
Sub:{ .m[X:mut](x: Box[read X]): Box[read/imm X] -> x; .n[X:mut](x: Box[read/imm X]): Box[read X] -> x }
"""));}
@Test void typeArgumentReadImmXEqualsXWhenBoundHasOnlyImm(){ok(List.of("""
Box[T:*]:{}
Sub:{ .m[X:imm](x: Box[X]): Box[read/imm X] -> x; .n[X:imm](x: Box[read/imm X]): Box[X] -> x }
"""));}
@Test void typeArgumentReadImmXEqualsXWhenBoundHasOnlyReadImm(){ok(List.of("""
Box[T:*]:{}
Sub:{ .m[X:read,imm](x: Box[X]): Box[read/imm X] -> x; .n[X:read,imm](x: Box[read/imm X]): Box[X] -> x }
"""));}
@Test void typeArgumentReadImmXEqualsImmXWhenBoundHasOnlyIsoImm(){ok(List.of("""
Box[T:*]:{}
Sub:{ .m[X:iso,imm](x: Box[imm X]): Box[read/imm X] -> x; .n[X:iso,imm](x: Box[read/imm X]): Box[imm X] -> x }
"""));}
@Test void typeArgumentReadImmXDiffersFromXWhenBoundHasIso(){fail("""
002| Sub:{ .m[X:iso,imm](x: Box[X]): Box[read/imm X] -> x }
   |       ---------------------------------------------^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "Sub" is an expression returning "Box[X]".
Parameter "x" has type "Box[X]" instead of a subtype of "Box[read/imm X]".

See inferred typing context below for how type "Box[read/imm X]" was introduced: (compression indicated by `-`)
Sub:{.m[X:imm,iso](x:Box[X]):Box[read/imm X]->x}
""",List.of("""
Box[T:**]:{}
Sub:{ .m[X:iso,imm](x: Box[X]): Box[read/imm X] -> x }
"""));}
}
