package inferenceGrammar;

import static org.junit.jupiter.api.Assertions.*;
import org.junit.jupiter.api.Test;

public class TestGamma {

  private static IT X(String name) { return new IT.X(name); }

  // 1) Root: declare, get, update change the signature appropriately
  @Test public void root_declare_get_update_and_signature() {
    Gamma g = new Gamma();

    Gamma.GammaSignature s0 = new Gamma.GammaSignature();
    g.sign(s0);

    g.declare("x", X("A"));
    assertFalse(g.represents(s0), "declaring x must change signature");

    Gamma.GammaSignature s1 = new Gamma.GammaSignature();
    g.sign(s1);

    IT t2 = X("Foo");
    g.update("x", t2);
    assertFalse(g.represents(s1), "updating x must change signature");
    assertSame(t2, g.get("x"));
  }

  // 2) Inner declare does not affect parent after pop (sign/represents)
  @Test public void inner_declare_does_not_affect_parent_after_pop() {
    Gamma g = new Gamma();
    g.declare("x", X("X"));

    Gamma.GammaSignature parentBefore = new Gamma.GammaSignature();
    g.sign(parentBefore);

    g.newScope();
    Gamma.GammaSignature childStart = new Gamma.GammaSignature();
    g.sign(childStart);
    assertTrue(g.represents(parentBefore), "child inherits parent signature at scope push");

    g.declare("y", X("MapQ"));
    assertFalse(g.represents(childStart), "child sees its own declare");

    g.popScope();
    assertTrue(g.represents(parentBefore), "parent signature must match again after popping child");
  }

  // 3) Update of outer var is visible to child and remains visible after pop
  @Test public void update_of_outer_var_is_visible_to_child_and_remains_after_pop() {
    Gamma g = new Gamma();
    g.declare("x", X("X"));

    Gamma.GammaSignature parentBefore = new Gamma.GammaSignature();
    g.sign(parentBefore);

    g.newScope();
    Gamma.GammaSignature childBefore = new Gamma.GammaSignature();
    g.sign(childBefore);

    IT t2 = X("Foo");
    g.update("x", t2); // x declared at parent depth

    assertFalse(g.represents(childBefore), "child must see parent var update");

    g.popScope();
    assertFalse(g.represents(parentBefore), "parent signature must reflect the update after pop");
    assertSame(t2, g.get("x"));
  }

  // 4) Three-scope visibility: updates only affect scopes that can see the binding
  @Test public void three_scopes_visibility_matrix_with_signatures() {
    Gamma g = new Gamma();
    g.declare("x", X("X0"));
    Gamma.GammaSignature sigRootAfterX = new Gamma.GammaSignature();
    g.sign(sigRootAfterX);

    g.newScope(); // depth 2
    g.declare("y", X("Y0"));
    g.declare("z", X("Z0")); // declare z at middle depth
    Gamma.GammaSignature sigMidAfterYZ = new Gamma.GammaSignature();
    g.sign(sigMidAfterYZ);

    g.newScope(); // depth 3
    Gamma.GammaSignature sigInnerBefore = new Gamma.GammaSignature();
    g.sign(sigInnerBefore);

    // Update z (declared at middle). Only inner (and middle) should change now.
    g.update("z", X("Z1"));
    assertFalse(g.represents(sigInnerBefore), "inner must change due to z update at middle");

    g.popScope(); // back to middle
    assertFalse(g.represents(sigMidAfterYZ), "middle must reflect its own z update");

    g.popScope(); // back to root
    assertTrue(g.represents(sigRootAfterX), "root should be unchanged by middle-only updates after pop");
  }

  // 5) get on unknown throws by design
  @Test public void get_unknown_throws_by_design() {
    Gamma g = new Gamma();
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("nope"));
  }

  // 6) update on unknown throws by design
  @Test public void update_unknown_throws_by_design() {
    Gamma g = new Gamma();
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.update("nope", X("T")));
  }

  // 7) duplicate declare fails with assertion if enabled
  @Test public void duplicate_declare_fails_with_assertion_if_enabled() {
    Gamma g = new Gamma();
    g.declare("x", X("A"));
    assertThrows(AssertionError.class, () -> g.declare("x", X("Foo")));
  }

  // 8) pop root fails with assertion if enabled
  @Test public void pop_root_fails_with_assertion_if_enabled() {
    Gamma g = new Gamma();
    assertThrows(AssertionError.class, g::popScope);
  }

  // 9) Large scope; threshold crossing; update seen across scopes; no leaks after pop
  @Test public void large_scope_correctness_under_many_binds_and_pops() {
    Gamma g = new Gamma();
    int n = 64;
    for (int i = 0; i < n; i++) g.declare("v" + i, X("T" + i));

    Gamma.GammaSignature sigParent = new Gamma.GammaSignature();
    g.sign(sigParent);

    assertSame(g.get("v0"), g.get("v0"));
    assertSame(g.get("v31"), g.get("v31"));
    assertSame(g.get("v63"), g.get("v63"));

    g.newScope();
    Gamma.GammaSignature sigChildStart = new Gamma.GammaSignature();
    g.sign(sigChildStart);
    assertTrue(g.represents(sigParent)); // child inherits parent

    IT t = X("T_updated");
    g.update("v31", t);
    assertFalse(g.represents(sigChildStart)); // child sees update

    // Snapshot child's post-update signature; after pop, parent should match it
    Gamma.GammaSignature sigChildAfter = new Gamma.GammaSignature();
    g.sign(sigChildAfter);

    g.popScope();
    assertTrue(g.represents(sigChildAfter), "update to parent-declared var must remain after pop");
    assertSame(t, g.get("v31"));

    g.newScope();
    for (int i = 0; i < 10; i++) g.declare("w" + i, X("W" + i));
    g.popScope();

    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("w0"));
    assertSame(t, g.get("v31"));

    // Inner-only declares should not disturb parent after pop
    assertTrue(g.represents(sigChildAfter));
  }

  // 10) Popped name get after slot reuse throws (stale index must not resurrect)
  @Test public void popped_name_get_after_slot_reuse_throws() {
    Gamma g = new Gamma();
    int base = 13;
    for (int i = 0; i < base; i++) g.declare("v" + i, X("V" + i));
    g.newScope();
    g.declare("w0", X("W0"));
    g.popScope(); // w0 out of scope
    g.declare("a0", X("A0")); // reuse slot
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("w0"));
  }

  // 11) Popped name update after slot reuse throws
  @Test public void popped_name_update_after_slot_reuse_throws() {
    Gamma g = new Gamma();
    int base = 13;
    for (int i = 0; i < base; i++) g.declare("v" + i, X("V" + i));
    g.newScope();
    g.declare("w0", X("W0"));
    g.popScope(); // w0 out of scope
    IT a0 = X("A0");
    g.declare("a0", a0);
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.update("w0", X("POISON")));
    assertSame(a0, g.get("a0"));
  }

  // 12) Update with the same value is a no-op for the signature
  @Test public void update_with_same_value_is_noop_for_signature() {
    Gamma g = new Gamma();
    g.declare("x", X("X"));
    Gamma.GammaSignature before = new Gamma.GammaSignature();
    g.sign(before);
    g.update("x", X("X")); // equals, no change
    assertTrue(g.represents(before), "updating to an equal value must not change signature");
  }

  // 13) Declaring "_" must be a no-op for the signature and name table
  @Test public void underscore_declare_is_noop() {
    Gamma g = new Gamma();
    Gamma.GammaSignature before = new Gamma.GammaSignature();
    g.sign(before);
    g.declare("_", X("IGNORED"));
    assertTrue(g.represents(before), "declaring '_' must not change signature");
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("_"));
  }

  // 14) Commutativity of declares: same bindings, different order => same signature
  @Test public void same_bindings_different_order_same_signature() {
    // This test compares raw hashes from two independent Gammas.
    Gamma g1 = new Gamma();
    g1.declare("a", X("A"));
    g1.declare("b", X("B"));
    Gamma.GammaSignature sAB = new Gamma.GammaSignature();
    g1.sign(sAB);

    Gamma g2 = new Gamma();
    g2.declare("b", X("B"));
    g2.declare("a", X("A"));
    Gamma.GammaSignature sBA = new Gamma.GammaSignature();
    g2.sign(sBA);

    assertEquals(sAB.hash, sBA.hash, "hash must be order-independent across declares");
  }

  // 15) snapshot/changed semantics: changed should be false after snapshot, true after a change
  @Test public void snapshot_and_changed_semantics() {
    Gamma g = new Gamma();
    long s= g.snapshot();
    assertFalse(g.changed(s), "immediately after snapshot, changed() should be false");
    g.declare("x", X("X"));
    assertTrue(g.changed(s), "after a change, changed() should be true");
  }
}