package main;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.net.URI;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import core.E.Literal;
import core.TName;
import main.FrontendLogicMain.TestSource;
import metaParser.Layout;
import testUtils.DbgBlock;
import tools.SourceOracle;
import utils.Join;

public final class GeneratedTestsTest extends testUtils.FearlessTestBase{
  static final String pkg= """
A:{ .m: A -> this; .n: A -> A{ .m -> this } }
_H:{ .h: _H -> this }
S:base.Sealed{ .s: S -> this }
""";
  static final URI testsUri= URI.create("fear:/___DBG___/p_test.fear");
  static SourceOracle tests(String src){ return SourceOracle.debugBuilder().putURI(testsUri, src).build(); }
  static List<Literal> compile(String tests){ return compile(List.of(pkg), List.of(new TestSource(testsUri, tests, Layout.same))); }
  static List<Literal> compile(List<String> pkgFiles, List<TestSource> tests){
    var o= oraclePkg(pkgFiles);
    return new FrontendLogicMain().of("p", Map.of(), o.allFiles(), otherFrom(DbgBlock.all()), _ -> tests);
  }
  static String names(List<Literal> core){ return Join.of(AllLs.of(core).keySet().stream().map(TName::s).sorted(), "", "\n", "\n", ""); }
  static void ok(String expected, String tests){
    var o= oraclePkg(List.of(pkg)).withFallback(tests(tests));
    strCmp(expected, names(okOrPrint(o, () -> compile(tests))));
  }
  static void fail(String expected, String tests){
    var o= oraclePkg(List.of(pkg)).withFallback(tests(tests));
    var fe= assertThrows(FearlessException.class, () -> compile(tests));
    strCmp(expected, fe.render(o));
  }
  @Test void noTestsCompilesThePackageAlone(){
    var o= oraclePkg(List.of(pkg));
    strCmp("""
p.A
p.S
p._AA
p._H
""", names(new FrontendLogicMain().of("p", Map.of(), o.allFiles(), otherFrom(DbgBlock.all()), _ -> List.of())));
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
In file: fear:/___DBG___/p_test.fear

001| A:{}
   | ^^

While inspecting a type name
Duplicate type declaration for "A".
Error 7 WellFormedness
""", """
A:{}
"""); }
  @Test void anErrorInTheTestsIsReportedInTheTestsFile(){ fail("""
In file: fear:/___DBG___/p_test.fear

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
  static final String pkgDocs= pkg+"""
///Calls a missing method.
//> A.zz
""";
  static final String other= """
B:{ .b: B -> this }
//> B.zz
""";
  record At(int line, int column, boolean shifted){}
  static At fixed(int line, int column){ return new At(line, column, false); }
  static At shifted(int line, int column){ return new At(line, column, true); }
  static Layout layout(At... lines){
    return new Layout(){
      @Override public int line(int line){ return lines[line-1].line(); }
      @Override public int column(int line, int column){ return lines[line-1].shifted() ? lines[line-1].column()+column-1 : lines[line-1].column(); }
    };
  }
  static TestSource at(int file, String text, At... lines){ return new TestSource(SourceOracle.defaultDbgFearPath(file), text, layout(lines)); }
  static void failAt(String expected, List<String> pkgFiles, TestSource... tests){
    var fe= assertThrows(FearlessException.class, () -> compile(pkgFiles, List.of(tests)));
    strCmp(expected, fe.render(oraclePkg(pkgFiles)));
  }
  @Test void anErrorOnAShiftedLineIsReportedWhereThatTextIsInThePackage(){ failAt("""
In file: fear:/___DBG___/_rank_app999.fear

005| //> A.zz
   |     -^^^

While inspecting ".a" line 5
This call to method ".zz" cannot typecheck.
Method ".zz" is not declared on type "A".

Available methods on type "A":
-       .m:A
-       .n:A

Compressed relevant code with inferred types: (compression indicated by `-`)
A.zz
Error 8 TypeError
""", List.of(pkgDocs), at(0, "T:{ .a: A ->\nA.zz\n  }", fixed(5, 5), shifted(5, 5), fixed(5, 9))); }
  @Test void anUnclosedGroupIsReportedWhereItsOpenerIsInThePackage(){ failAt("""
In file: fear:/___DBG___/_rank_app999.fear

005| //> A.zz
   |        ^

While inspecting groups of parenthesis
File ended while parsing a "{" group.
This "{" may be unintended.
Otherwise expected one of: "}id", "}".
Error 0 Unclosed
""", List.of(pkgDocs), at(0, "T:{ .a: A ->\nA.m{", fixed(5, 5), shifted(5, 5))); }
  @Test void testsFromTwoFilesAreReportedInTheirOwnFile(){ failAt("""
In file: fear:/___DBG___/in_memory1.fear

002| //> B.zz
   |     -^^^

While inspecting ".u" line 2
This call to method ".zz" cannot typecheck.
Method ".zz" is not declared on type "B".

Available methods on type "B":
-       .b:B

Compressed relevant code with inferred types: (compression indicated by `-`)
B.zz
Error 8 TypeError
""", List.of(pkgDocs, other), at(0, "T:{ .a: A ->\nA.m\n  }", fixed(5, 5), shifted(5, 5), fixed(5, 8)), at(1, "U:{ .u: B ->\nB.zz\n  }", fixed(2, 5), shifted(2, 5), fixed(2, 9))); }
  @Test void testsFromTwoFilesSeeEachOther(){
    var core= compile(List.of(pkgDocs, other), List.of(
      at(0, "T:{ .a: A ->\nA.m\n  }", fixed(5, 5), shifted(5, 5), fixed(5, 8)),
      at(1, "U:{ .u: T ->\nT\n  }", fixed(2, 5), shifted(2, 5), fixed(2, 6))));
    strCmp("""
p.A
p.B
p.S
p.T
p.U
p._AA
p._H
""", names(core));
  }
}
