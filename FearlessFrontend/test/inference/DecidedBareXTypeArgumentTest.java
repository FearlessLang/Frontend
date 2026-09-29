package inference;

import java.util.List;

import org.junit.jupiter.api.Test;

public class DecidedBareXTypeArgumentTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }

@Test void funnellingLiteralKeepsBareXReturn(){ok(List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](b: Box[X]): mut Get[X] -> mut Fresh[X:imm,mut,read]:Get[X]{ .get -> b.get } }
"""));}
@Test void funnellingLiteralWithExplicitSignatureOk(){ok(List.of("""
Box[X:imm]:{ .get: X }
Get[X:imm,mut,read]:{ mut .get: X }
A:{ .m[X:imm](b: Box[X]): mut Get[X] -> mut Fresh[X:imm,mut,read]:Get[X]{ mut .get: X -> b.get } }
"""));}
}