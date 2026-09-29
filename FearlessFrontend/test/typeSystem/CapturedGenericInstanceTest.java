package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class CapturedGenericInstanceTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }

@Test void immCaptureOfGenericInstanceInReadMethodOfWiderBoundLiteral(){ok(List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ read .get: read/imm X }
A:{ .m[X:imm](b: Box[X]): read Get[X] -> read Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
"""));}
@Test void mutCaptureOfGenericInstanceInMutMethodOfWiderBoundLiteral(){ok(List.of("""
Box[X:imm]:{ mut .get: X }
Get[X:imm,mut,read]:{ mut .get: read/imm X }
A:{ .m[X:imm](b: mut Box[X]): mut Get[X] -> mut Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
"""));}
@Test void immCaptureOfGenericInstanceInLiteralNestedInWiderBoundLiteral(){ok(List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ .get: read/imm X }
A:{ .m[X:imm](b: Box[X]): Get[X] -> Fresh[X:imm,mut,read]:Get[X]{ .get -> Inner[X:imm,mut,read]:Get[X]{ .get -> b.get }.get } }
"""));}
}
