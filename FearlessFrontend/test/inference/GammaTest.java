package inference;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import java.util.List;

import core.RC;
import utils.Range;

public final class GammaTest{

  private static IT X(String name){ return new IT.X(name, null); }

  // 1) Root: declare, get, update change the signature appropriately
  @Test void root_declare_get_update_and_signature(){
    var g= new Gamma();

    var s0= new Gamma.GammaSignature();
    g.sign(s0);

    g.declare("x", X("A"));
    assertFalse(g.represents(s0), "declaring x must change signature");

    var s1= new Gamma.GammaSignature();
    g.sign(s1);

    var t2= X("Foo");
    g.update("x", t2);
    assertTrue(g.represents(s1), "updating x must not change signature");
    assertSame(t2, g.learned("x"));
  }

  // 2) Inner declare does not affect parent after pop (sign/represents)
  @Test void inner_declare_does_not_affect_parent_after_pop(){
    var g= new Gamma();
    g.declare("x", X("X"));

    var parentBefore= new Gamma.GammaSignature();
    g.sign(parentBefore);

    g.newScope(RC.mut, List.of(), null);
    var childStart= new Gamma.GammaSignature();
    g.sign(childStart);
    assertTrue(g.represents(parentBefore), "child inherits parent signature at scope push");

    g.declare("y", X("MapQ"));
    assertFalse(g.represents(childStart), "child sees its own declare");

    g.popScope();
    assertTrue(g.represents(parentBefore), "parent signature must match again after popping child");
  }

  // 3) Update of outer var is part of no signature and remains learned after pop
  @Test void update_of_outer_var_is_in_no_signature_and_remains_after_pop(){
    var g= new Gamma();
    g.declare("x", X("X"));

    var parentBefore= new Gamma.GammaSignature();
    g.sign(parentBefore);

    g.newScope(RC.mut, List.of(), null);
    var childBefore= new Gamma.GammaSignature();
    g.sign(childBefore);

    var t2= X("Foo");
    g.update("x", t2); // x declared at parent depth

    assertTrue(g.represents(childBefore), "the update is not part of the child signature");

    g.popScope();
    assertTrue(g.represents(parentBefore), "the update is not part of the parent signature");
    assertSame(t2, g.learned("x"));
  }

  // 5) get on unknown throws by design
  @Test void get_unknown_throws_by_design(){
    var g= new Gamma();
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("nope"));
  }

  // 6) update on unknown throws by design
  @Test void update_unknown_throws_by_design(){
    var g= new Gamma();
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.update("nope", X("T")));
  }

  // 7) duplicate declare fails with assertion if enabled
  @Test void duplicate_declare_fails_with_assertion_if_enabled(){
    var g= new Gamma();
    g.declare("x", X("A"));
    assertThrows(AssertionError.class, () -> g.declare("x", X("Foo")));
  }

  // 8) pop root fails with assertion if enabled
  @Test void pop_root_fails_with_assertion_if_enabled(){
    var g= new Gamma();
    assertThrows(AssertionError.class, g::popScope);
  }

  // 9) Large scope; threshold crossing; update seen across scopes; no leaks after pop
  @Test void large_scope_correctness_under_many_binds_and_pops(){
    var g= new Gamma();
    int n= 64;
    for (int i : Range.of(0, n)){ g.declare("v"+i, X("T"+i)); }

    var sigParent= new Gamma.GammaSignature();
    g.sign(sigParent);

    assertSame(g.get("v0"), g.get("v0"));
    assertSame(g.get("v31"), g.get("v31"));
    assertSame(g.get("v63"), g.get("v63"));

    g.newScope(RC.mut, List.of(), null);
    var sigChildStart= new Gamma.GammaSignature();
    g.sign(sigChildStart);
    assertTrue(g.represents(sigParent)); // child inherits parent

    var t= X("T_updated");
    g.update("v31", t);
    assertTrue(g.represents(sigChildStart));

    // Snapshot child's post-update signature; after pop, parent should match it
    var sigChildAfter= new Gamma.GammaSignature();
    g.sign(sigChildAfter);

    g.popScope();
    assertTrue(g.represents(sigChildAfter), "update to parent-declared var must remain after pop");
    assertSame(t, g.learned("v31"));

    g.newScope(RC.mut, List.of(), null);
    for (int i : Range.of(0, 10)){ g.declare("w"+i, X("W"+i)); }
    g.popScope();

    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("w0"));
    assertSame(t, g.learned("v31"));

    // Inner-only declares should not disturb parent after pop
    assertTrue(g.represents(sigChildAfter));
  }

  // 10) Popped name get after slot reuse throws (stale index must not resurrect)
  @Test void popped_name_get_after_slot_reuse_throws(){
    var g= new Gamma();
    int base= 13;
    for (int i : Range.of(0, base)){ g.declare("v"+i, X("V"+i)); }
    g.newScope(RC.mut, List.of(), null);
    g.declare("w0", X("W0"));
    g.popScope(); // w0 out of scope
    g.declare("a0", X("A0")); // reuse slot
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("w0"));
  }

  // 11) Popped name update after slot reuse throws
  @Test void popped_name_update_after_slot_reuse_throws(){
    var g= new Gamma();
    int base= 13;
    for (int i : Range.of(0, base)){ g.declare("v"+i, X("V"+i)); }
    g.newScope(RC.mut, List.of(), null);
    g.declare("w0", X("W0"));
    g.popScope(); // w0 out of scope
    var a0= X("A0");
    g.declare("a0", a0);
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.update("w0", X("POISON")));
    assertSame(a0, g.get("a0"));
  }

  // 12) The late pass makes the signatures of the first pass stale
  @Test void late_pass_makes_first_pass_signatures_stale(){
    var g= new Gamma();
    g.declare("x", X("X"));
    var first= new Gamma.GammaSignature();
    g.sign(first);
    assertFalse(g.late());
    g.latePass();
    assertTrue(g.late());
    assertFalse(g.represents(first), "a signature of the first pass must not represent the late pass");
    var late= new Gamma.GammaSignature();
    g.sign(late);
    assertTrue(g.represents(late));
  }

  // 13) Declaring "_" must be a no-op for the signature and name table
  @Test void underscore_declare_is_noop(){
    var g= new Gamma();
    var before= new Gamma.GammaSignature();
    g.sign(before);
    g.declare("_", X("IGNORED"));
    assertTrue(g.represents(before), "declaring '_' must not change signature");
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("_"));
  }

  // 14) Commutativity of declares: same bindings, different order => same signature
  @Test void same_bindings_different_order_same_signature(){
    // This test compares raw hashes from two independent Gammas.
    var g1= new Gamma();
    g1.declare("a", X("A"));
    g1.declare("b", X("B"));
    var sAB= new Gamma.GammaSignature();
    g1.sign(sAB);

    var g2= new Gamma();
    g2.declare("b", X("B"));
    g2.declare("a", X("A"));
    var sBA= new Gamma.GammaSignature();
    g2.sign(sBA);

    assertEquals(sAB.shot, sBA.shot, "signature must be order-independent across declares");
  }

  // 16) Nesting and bindings grow past the initial capacities
  @Test void deep_scopes_and_many_bindings_grow(){
    var g= new Gamma();
    var root= new Gamma.GammaSignature();
    g.sign(root);
    int n= 1000;
    for (int i : Range.of(0, n)){
      g.newScope(RC.mut, List.of(), null);
      for (int j : Range.of(0, 10)){ g.declare("v"+i+"_"+j, X("T"+i)); }
    }
    assertEquals(X("T0"), g.get("v0_0"));
    assertEquals(X("T999"), g.get("v999_9"));
    g.update("v0_0", X("U"));
    assertEquals(X("U"), g.learned("v0_0"));
    for (int _ : Range.of(0, n)){ g.popScope(); }
    assertTrue(g.represents(root));
    assertThrows(ArrayIndexOutOfBoundsException.class, () -> g.get("v0_0"));
  }
}