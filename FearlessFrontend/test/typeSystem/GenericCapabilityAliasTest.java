package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class GenericCapabilityAliasTest extends testUtils.FearlessTestBase{
  private static final String cellAndBox= """
Cell:{ read .get:base.Nat; mut .set(value:base.Nat):base.Void; }
Box[X:imm,mut]:{ mut .get:X; }
Boxes:{ #(cell:mut Cell):mut Box[mut Cell] ->
  mut Box[mut Cell]{ mut .get -> cell; }
}
""";
  static void ok(String user){ typeOk(List.of(cellAndBox + user)); }
  static void fail(String expected, String user){ typeFail(expected, List.of(cellAndBox + user)); }

@Test void capturedMutableCellStaysMutable(){ok("""
User:{ .get(cell:mut Cell):mut Cell->(Boxes#cell).get; }
""");}
@Test void boxReceiverCapabilityStillWeakens(){ok("""
User:{ .weaken(box:mut Box[mut Cell]):read Box[mut Cell]->box; }
""");}
@Test void rejectsDirectMutableToImmutableAlias(){fail("""
006| User:{ .freeze(cell:mut Cell):imm Cell->cell; }
   |        ---------------------------------^^^^^

While inspecting parameter "cell" > ".freeze(_)" line 6
The body of method ".freeze(_)" of type declaration "User" is an expression returning "mut Cell".
Parameter "cell" has type "mut Cell" instead of a subtype of "imm Cell".

See inferred typing context below for how type "Cell" was introduced: (compression indicated by `-`)
User:{.freeze(cell:mut Cell):Cell->cell}
""","""
User:{ .freeze(cell:mut Cell):imm Cell->cell; }
""");}
@Test void rejectsImmutableAliasToCapturedMutableCell(){fail("""
006| User:{ .freeze(box:mut Box[mut Cell]):mut Box[imm Cell]->box; }
   |        --------------------------------------------------^^^^

While inspecting parameter "box" > ".freeze(_)" line 6
The body of method ".freeze(_)" of type declaration "User" is an expression returning "mut Box[mut Cell]".
Parameter "box" has type "mut Box[mut Cell]" instead of a subtype of "mut Box[Cell]".

See inferred typing context below for how type "mut Box[Cell]" was introduced: (compression indicated by `-`)
User:{.freeze(box:mut Box[mut Cell]):mut Box[Cell]->box}
""","""
User:{ .freeze(box:mut Box[mut Cell]):mut Box[imm Cell]->box; }
""");}
@Test void rejectsMutableAliasToImmutableArgument(){fail("""
006| User:{ .thaw(box:mut Box[imm Cell]):mut Box[mut Cell]->box; }
   |        ------------------------------------------------^^^^

While inspecting parameter "box" > ".thaw(_)" line 6
The body of method ".thaw(_)" of type declaration "User" is an expression returning "mut Box[Cell]".
Parameter "box" has type "mut Box[Cell]" instead of a subtype of "mut Box[mut Cell]".

See inferred typing context below for how type "mut Box[mut Cell]" was introduced: (compression indicated by `-`)
User:{.thaw(box:mut Box[Cell]):mut Box[mut Cell]->box}
""","""
User:{ .thaw(box:mut Box[imm Cell]):mut Box[mut Cell]->box; }
""");}
}
