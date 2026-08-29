package typeSystem;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import main.FrontendLogicMain;
import testUtils.DbgBlock;

public class TypeInMethodTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }

  static void okTwoPkgs(String aSrc, String bSrc){
    var oB= oraclePkg(List.of(bSrc));
    okOrPrint(oB, ()->compileB(aSrc, oB));
  }
  static void failTwoPkgs(String expected, String aSrc, String bSrc){
    var oB= oraclePkg(List.of(bSrc));
    var fe= assertThrows(FearlessException.class, ()->compileB(aSrc, oB));
    strCmp("In file: [###].fear\n\n"+expected+"Error 8 TypeError", fe.render(oB));
  }
  private static List<core.E.Literal> compileB(String aSrc, tools.SourceOracle oB){
    var base= otherFrom(DbgBlock.all());
    var oA= oraclePkg(List.of(aSrc));
    var aLits= okOrPrint(oA, ()->compileAll("a", oA, base));
    var other= base.mergeWith(AllLs.of(aLits), -1);
    return new FrontendLogicMain().of("b", Map.of(), oB.allFiles(), oB, other);
  }
  private static final String byName= """
002| B:{.m:A->A}
   |    ------^^

While inspecting object literal instance of "A" > ".m" line 2
The type "A" is declared inside a method body.
A type declared inside a method can capture any parameter name in scope,
so it can not be extended or instantiated.
Hint: if it captures nothing, declare it implementing "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
A
""";
  private static final String byNameOtherPkg= """
001| B:{.m:a.A->a.A}
   |    --------^^^^

While inspecting object literal instance of "a.A" > ".m" line 1
The type "a.A" is declared inside a method body.
A type declared inside a method can capture any parameter name in scope,
so it can not be extended or instantiated.
Hint: if it captures nothing, declare it implementing "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
-.A
""";

  @Test void topLevelTypeByName(){ ok(List.of("""
A:{}
B:{.m:A->A}
""")); }

  @Test void captureFreeTypeInMethodByName(){ ok(List.of("""
A0:{.m:A->A:base.CaptureFree{}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodNeverInstantiated(){ ok(List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""")); }

  @Test void typeInMethodCapturingThisByName(){ fail(byName,List.of("""
A0:{.m:A->A:{.foo:A0->this}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodCapturingParameterByName(){ fail(byName,List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodCapturingNothingByName(){ fail(byName,List.of("""
A0:{.m:A->A:{}}
B:{.m:A->A}
""")); }

  @Test void typeInMethodExtended(){ fail("""
002| B:A{}
   | ^^^^^

While inspecting type declaration "B"
The type "A" is declared inside a method body.
A type declared inside a method can capture any parameter name in scope,
so it can not be extended or instantiated.
Hint: if it captures nothing, declare it implementing "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
B:A{}
""",List.of("""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
B:A{}
""")); }

  @Test void captureFreeTypeInMethodExtended(){ ok(List.of("""
A0:{.m:A->A:base.CaptureFree{}}
B:A{}
""")); }

  @Test void topLevelTypeByNameFromOtherPkg(){ okTwoPkgs("""
A:{}
""","""
B:{.m:a.A->a.A}
"""); }

  @Test void captureFreeTypeInMethodByNameFromOtherPkg(){ okTwoPkgs("""
A0:{.m:A->A:base.CaptureFree{}}
""","""
B:{.m:a.A->a.A}
"""); }

  @Test void typeInMethodCapturingThisByNameFromOtherPkg(){ failTwoPkgs(byNameOtherPkg,"""
A0:{.m:A->A:{.foo:A0->this}}
""","""
B:{.m:a.A->a.A}
"""); }

  @Test void typeInMethodCapturingParameterByNameFromOtherPkg(){ failTwoPkgs(byNameOtherPkg,"""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""","""
B:{.m:a.A->a.A}
"""); }

  @Test void typeInMethodExtendedFromOtherPkg(){ failTwoPkgs("""
001| B:a.A{}
   | ^^^^^^^

While inspecting type declaration "B"
The type "a.A" is declared inside a method body.
A type declared inside a method can capture any parameter name in scope,
so it can not be extended or instantiated.
Hint: if it captures nothing, declare it implementing "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
B:-.A{}
""","""
A0:{.m(x:A0):A->A:{.foo:A0->x}}
""","""
B:a.A{}
"""); }
}
