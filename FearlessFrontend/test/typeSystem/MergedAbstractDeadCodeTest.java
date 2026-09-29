package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class MergedAbstractDeadCodeTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
@Test void immLiteralTwoSupersLeaveSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:{ mut .m: A }
User:{ #: A -> C:A,B{} }
"""));}
@Test void readLiteralTwoSupersLeaveSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:{ mut .m: A }
User:{ #: read A -> read C:A,B{} }
"""));}
@Test void readLiteralDiamondLeavesSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:A{}
D:A{}
User:{ #: read A -> read C:B,D{} }
"""));}
@Test void readLiteralImplementsReadOverloadOfMergedMutAbstract(){ok(List.of("""
Z:{}
A:{ mut .m: Z; read .m: Z }
B:{ mut .m: Z; read .m: Z }
User:{ #: read A -> read C:A,B{ .m -> Z } }
"""));}
}