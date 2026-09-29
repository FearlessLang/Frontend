package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class ReadImmTypeArgumentTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }

@Test void typeArgumentReadImmXEqualsReadXWhenBoundHasOnlyMut(){ok(List.of("""
Box[T:*]:{}
Sub:{ .m[X:mut](x: Box[read X]): Box[read/imm X] -> x; .n[X:mut](x: Box[read/imm X]): Box[read X] -> x }
"""));}
@Test void typeArgumentReadImmXEqualsXWhenBoundHasOnlyImm(){ok(List.of("""
Box[T:*]:{}
Sub:{ .m[X:imm](x: Box[X]): Box[read/imm X] -> x; .n[X:imm](x: Box[read/imm X]): Box[X] -> x }
"""));}
}
