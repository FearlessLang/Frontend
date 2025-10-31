package inferenceGrammar;

import static org.junit.jupiter.api.Assertions.*;
import org.junit.jupiter.api.Test;
public class TestGamma {
  private static IT X(String name) { return new IT.X(name); }

  @Test public void root_declare_get_update_and_version() {
    Gamma g= new Gamma();
    long v0= g.visibleVersion();
    g.declare("x", X("A"));
    long v1= g.visibleVersion();
    assertNotEquals(v0, v1, "declaring x must stamp a new visible version");
    IT t2= X("Foo");
    g.update("x", t2);
    long v2= g.visibleVersion();
    assertNotEquals(v1, v2, "updating x must stamp a new visible version");
    assertTrue(v2 > v1);
    assertSame(t2, g.get("x"));
  }
  @Test public void inner_declare_does_not_affect_parent_version_after_pop(){
    Gamma g= new Gamma();
    g.declare("x", X("X"));
    long parentBefore= g.visibleVersion();
    g.newScope();
    long childStart= g.visibleVersion();
    assertEquals(parentBefore, childStart, "child inherits parent version");
    g.declare("y", X("MapQ"));
    long childAfter = g.visibleVersion();
    assertNotEquals(childStart, childAfter, "child sees its own declare");
    g.popScope();
    long parentAfter= g.visibleVersion();
    assertEquals(parentBefore, parentAfter, "parent must not see child-only declare after pop");
  }
  @Test public void update_of_outer_var_is_visible_to_child_and_remains_visible_after_pop(){
    Gamma g= new Gamma();
    g.declare("x", X("X"));
    long parentBefore= g.visibleVersion();
    g.newScope();
    long childBefore= g.visibleVersion();
    assertEquals(parentBefore, childBefore);
    IT t2 = X("Foo");
    g.update("x", t2); // x declared at parent depth
    long childAfter= g.visibleVersion();
    assertNotEquals(childBefore, childAfter, "child must see parent var update");
    g.popScope();
    long parentAfter= g.visibleVersion();
    assertEquals(childAfter, parentAfter, "same stamp should be visible to parent after pop");
    assertSame(t2, g.get("x"));
  }
  @Test public void three_scopes_visibility_matrix() {
    Gamma g= new Gamma();
    g.declare("x", X("X0"));
    long vRootAfterX= g.visibleVersion();
    g.newScope();            // depth 2
    g.declare("y", X("Y0"));
    long vMidAfterY= g.visibleVersion();
    g.newScope();            // depth 3
    g.declare("z", X("Z0"));
    long vInnerAfterZDecl = g.visibleVersion();
    // Update z (declared at depth 2) -> only innermost sees change now
    g.update("z", X("Z1"));
    long vInnerAfterZUpd = g.visibleVersion();
    assertNotEquals(vInnerAfterZDecl, vInnerAfterZUpd);
    g.popScope();            // back to middle
    long vMidAfterPopZ = g.visibleVersion();
    assertEquals(vMidAfterY, vMidAfterPopZ,
        "middle scope must not change due to z-only churn after popping z");
    // Update y (declared at middle depth) -> middle sees change; root should not yet
    g.update("y", X("Y1"));
    long vMidAfterYUpd = g.visibleVersion();
    assertNotEquals(vMidAfterPopZ, vMidAfterYUpd);
    g.popScope();            // back to root
    long vRootAfterPopY = g.visibleVersion();
    assertEquals(vRootAfterX, vRootAfterPopY,
        "root should not change due to y-only updates after popping y");
    // Update x (declared at root) -> root sees change
    g.update("x", X("X1"));
    long vRootAfterXUpd = g.visibleVersion();
    assertNotEquals(vRootAfterPopY, vRootAfterXUpd);
  }
  @Test public void get_unknown_throws_by_design() {
    Gamma g= new Gamma();
    // get uses ts[indexOf(x)] and indexOf returns -1 for unknown; we expect AIOOBE.
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("nope"));
  }
  @Test public void update_unknown_throws_by_design() {
    Gamma g= new Gamma();
    // update does ts[i] where i = -1; we expect AIOOBE.
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.update("nope", X("T")));
  }
  @Test public void duplicate_declare_fails_with_assertion_if_enabled() {
    Gamma g= new Gamma();
    g.declare("x", X("A"));
    assertThrows(AssertionError.class, () -> g.declare("x", X("Foo")));
  }
  @Test public void pop_root_fails_with_assertion_if_enabled() {
    Gamma g= new Gamma();
    assertThrows(AssertionError.class, g::popScope);
  }
  @Test public void large_scope_correctness_under_many_binds_and_pops() {
    Gamma g= new Gamma();
    int n= 64;
    for (int i= 0; i < n; i++) {
      g.declare("v" + i, X("T" + i));
    }
    long v1= g.visibleVersion();
    assertSame(g.get("v0"), g.get("v0"));
    assertSame(g.get("v31"), g.get("v31"));
    assertSame(g.get("v63"), g.get("v63"));
    g.newScope();
    long childStart= g.visibleVersion();
    assertEquals(v1, childStart);
    IT t= X("T_updated");
    g.update("v31", t);
    long childAfter= g.visibleVersion();
    assertNotEquals(childStart, childAfter);
    g.popScope();
    long parentAfter= g.visibleVersion();
    assertEquals(childAfter, parentAfter);
    assertSame(t, g.get("v31"));
    g.newScope();
    for (int i= 0; i < 10; i++) g.declare("w" + i, X("W" + i));
    g.popScope();
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("w0"));
    assertSame(t, g.get("v31"));
    long v3 = g.visibleVersion();
    assertEquals(childAfter, v3, "parent version unchanged by inner-only declares after pop");
  }
  @Test public void popped_name_get_after_slot_reuse_throws(){
    Gamma g= new Gamma();
    int base= 13;
    for (int i= 0; i < base; i++){ g.declare("v" + i, X("V" + i)); }
    g.newScope();
    g.declare("w0", X("W0"));
    g.popScope(); // size shrinks; idx still contains "w0" -> oldIndex (stale)
    // Reuse the same slot by adding one more name; now stale index is < size again.
    g.declare("a0", X("A0"));
    // Correct behavior: w0 is out of scope -> get should throw.
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("w0"));
  }
  @Test public void popped_name_update_after_slot_reuse_throws(){
    Gamma g= new Gamma();
    // Make index active
    int base= 13;
    for(int i= 0; i < base; i++){ g.declare("v" + i, X("V" + i)); }
    g.newScope();
    g.declare("w0", X("W0"));
    g.popScope(); // stale idx entry remains
    // Reuse the slot
    IT a0= X("A0");
    g.declare("a0", a0);
    // Correct behavior: w0 is out of scope -> update should throw.
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.update("w0", X("POISON")));
    assertSame(a0, g.get("a0"));
  }
}