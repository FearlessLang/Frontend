package main;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.net.URI;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import core.E.Literal;
import testUtils.DbgBlock;
import tools.SourceOracle;
import utils.Join;

public final class GeneratedTestsTest extends testUtils.FearlessTestBase{
  static final String pkg= """
A:{ .m: A -> this; .n: A -> A{ .m -> this } }
_H:{ .h: _H -> this }
S:base.Sealed{ .s: S -> this }
""";
  static SourceOracle tests(String src){ return SourceOracle.debugBuilder().putURI(URI.create("fear:/___DBG___/auto_tests/p_test.fear"), src).build(); }
  static List<Literal> compile(String tests){
    var o= oraclePkg(List.of(pkg));
    var t= tests(tests);
    return new FrontendLogicMain().of("p", Map.of(), o.allFiles(), otherFrom(DbgBlock.all()), _->Optional.of(t.allFiles().getFirst()));
  }
  static String names(List<Literal> core){ return Join.of(AllLs.of(core).keySet().stream().map(n->n.s()).sorted(), "", "\n", "\n", ""); }
  static void ok(String expected, String tests){
    var o= oraclePkg(List.of(pkg)).withFallback(tests(tests));
    strCmp(expected, names(okOrPrint(o, ()->compile(tests))));
  }
  static void fail(String expected, String tests){
    var o= oraclePkg(List.of(pkg)).withFallback(tests(tests));
    var fe= assertThrows(FearlessException.class, ()->compile(tests));
    strCmp(expected, fe.render(o));
  }
  @Test void noTestsCompilesThePackageAlone(){
    var o= oraclePkg(List.of(pkg));
    strCmp("""
p.A
p.S
p._AA
p._H
""", names(new FrontendLogicMain().of("p", Map.of(), o.allFiles(), otherFrom(DbgBlock.all()), _->Optional.empty())));
  }
  @Test void testsSeeEveryTypeOfThePackage(){ ok("""
p.A
p.S
p.T
p._AA
p._AT
p._H
""", """
T:{ .a: A -> A.m; .h: _H -> _H.h; .s: S -> S.s; .n: A -> A{ .m -> A } }
"""); }
  @Test void freshNamesInTheTestsAvoidThoseOfThePackage(){ ok("""
p.A
p.A_
p.S
p._AA
p._BA
p._H
""", """
A_:{ .n: A -> A{ .m -> A } }
"""); }
  @Test void testsCanImplementSealedTypesOfThePackage(){ ok("""
p.A
p.S
p.S2
p._AA
p._H
""", """
S2:S{}
"""); }
  @Test void testsCanNotRedeclareATypeOfThePackage(){ fail("""
In file: fear:/___DBG___/auto_tests/p_test.fear

001| A:{}
   | ^^

While inspecting a type name
Duplicate type declaration for "A".
Error 7 WellFormedness
""", """
A:{}
"""); }
  @Test void anErrorInTheTestsIsReportedInTheTestsFile(){ fail("""
In file: fear:/___DBG___/auto_tests/p_test.fear

001| T:{ .a: A -> A.zz }
   |     ---------~^^^

While inspecting ".a" line 1
This call to method ".zz" cannot typecheck.
Method ".zz" is not declared on type "A".

Available methods on type "A":
-       .m:A
-       .n:A

Compressed relevant code with inferred types: (compression indicated by `-`)
A.zz
Error 8 TypeError
""", """
T:{ .a: A -> A.zz }
"""); }
}
