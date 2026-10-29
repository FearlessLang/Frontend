package main;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import core.OtherPackages;
import testUtils.DbgBlock;

public final class MapDirectiveTest extends testUtils.FearlessTestBase{
  static final String aA= "A:{.fromA:A->this}";
  static final String cA= "A:{.fromC:A->this}";
  static final String dA= "A:{.fromD:A->this}";
  static OtherPackages others(Map<String,String> pkgs){
    var res= otherFrom(DbgBlock.all());
    for (var e : pkgs.entrySet()){
      var o= oraclePkg(List.of(e.getValue()));
      var lits= compileAll(e.getKey(), o, otherFrom(DbgBlock.all()));
      res = res.mergeWith(AllLs.of(lits), -1);
    }
    return res;
  }
  static void ok(Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var res= okOrPrint(o, () -> new FrontendLogicMain().of("b", map, o.allFiles(), other));
    if (!checkCompact){ return; }
    coreCmp(lines(res), compact.Print.lines(compactB(pkgs, map, o)));
  }
  static void fail(String expected, Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var fe= assertThrows(FearlessException.class, () -> new FrontendLogicMain().of("b", map, o.allFiles(), other));
    strCmp(expected, fe.render(o));
    if (!checkCompact){ return; }
    assertThrows(compact.Frontend.Fail.class, () -> compactB(pkgs, map, o));
  }
  static List<compact.Frontend.Literal> compactB(Map<String,String> pkgs, Map<String,String> map, tools.SourceOracle o){
    var base= compactBase();
    var other= new ArrayList<>(base);
    for (var e : pkgs.entrySet()){ compactAll(e.getKey(), oraclePkg(List.of(e.getValue())), base).stream().flatMap(MapDirectiveTest::compactAllLs).forEach(other::add); }
    return compactAll("b", map, o, other);
  }
  @Test void typingContextShowsSupertypeWrittenThroughAMap(){ fail("""
In file: [###].fear

001| B:a.A{ .fromC -> base.Void }
   |        ----------^^^^^^^^^

While inspecting object literal instance of "base.Void" > ".fromC" line 1
The body of method ".fromC" of type declaration "B" is an expression returning "iso base.Void".
Object literal is of type "base.Void" instead of a subtype of "a.A".

Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:-.A{.fromC:-.A->-.Void}
Error 8 TypeError""", Map.of("c", cA), Map.of("a", "c"), """
B:a.A{ .fromC -> base.Void }
"""); }
  @Test void typeErrorWritesTheMappedName(){ fail("""
In file: [###].fear

001| B:{.k(x:a.A):B->x.m}
   |    -------------^^^^

While inspecting method call ".m" > ".k(_)" line 1
The body of method ".k(_)" of type declaration "B" is an expression returning "a.A".
Method call "a.A.m" has type "a.A" instead of a subtype of "B".

Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.k(x:-.A):B->x.m}
Error 8 TypeError""", Map.of("c", "A:{.m:A->this}"), Map.of("a", "c"), """
B:{.k(x:a.A):B->x.m}
"""); }
  @Test void inferenceErrorWritesTheMappedName(){ fail("""
In file: [###].fear

001| B:a.A,a.A2{}
   | ^^^^^^^^^^^^

While inspecting type declaration "B"
Return type disagreement for method "imm .m" with 0 parameters.
Different options are present in the implemented types: "a.A", "a.A2".
Type declaration "B" must declare a method ".m" explicitly choosing the desired option.

Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".
Type name "a.A2" in package "b" is mapped to the real source location "c.A2" because of "map a as c in b".
Error 7 WellFormedness""", Map.of("c", "A:{.m:A->this} A2:{.m:A2->this}"), Map.of("a", "c"), """
B:a.A,a.A2{}
"""); }
  @Test void mapToMissingTypeSuggestsNoNameTheMapRedirects(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):B->this}
   |         ^^^^

While inspecting a type name
Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".
Type "A" is not declared in package "c".
In scope: "C".
Error 7 WellFormedness
""", Map.of("c", "C:{}"), Map.of("a", "c"), """
B:{.m(x:a.A):B->this}
"""); }
  @Test void noMapQualifiedNameIsLiteral(){ ok(Map.of("a", aA, "c", cA), Map.of(), """
B:{.m(x:a.A):a.A->x.fromA}
"""); }
  @Test void mappedNameStandsForTheOutPackage(){ ok(Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void outPackageIsNotReachableByItsOwnName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):c.A->x.fromC}
   |              ^^^^

While inspecting a type name
Type "c.A" is written "a.A" in package "b", because of "map a as c in b".
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.A):c.A->x.fromC}
"""); }
  @Test void useOfTheCurrentPackage(){ fail("""
In file: [###].fear

001| use b.B as X;
   |     ^^^

While inspecting package header
"use" directive refers to type "B" of the current package "b".
A "use" directive can only refer to types of other packages: the types of package "b" are already in scope by their simple names.
Error 7 WellFormedness""", Map.of(), Map.of(), """
use b.B as X;
B:{.m(x:X):B->x.self; .self:X->this}
"""); }
  @Test void currentPackageQualified(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
Type "b.B" is written "B" in package "b", because the types of package "b" are written by their simple names.
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.B):B->this}
"""); }
  @Test void currentPackageQualifiedUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:b.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "b.Z" is written "Z" in package "b", because the types of package "b" are written by their simple names.
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.Z):B->this}
"""); }
  @Test void mapToMissingType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Type name "a.Z" in package "b" is mapped to the real source location "c.Z" because of "map a as c in b".
Type "Z" is not declared in package "c".
In scope: "A".
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.Z):B->this}
"""); }
  @Test void useThroughMap(){ ok(Map.of("c", cA), Map.of("a", "c"), """
use a.A as A;
B:{.m(x:A):A->x.fromC}
"""); }
  @Test void useThroughMapToMissingType(){ fail("""
In file: [###].fear

001| use a.Z as Z;
   |     ^^^

While inspecting package header
Type name "a.Z" in package "b" is mapped to the real source location "cc.Z" because of "map a as cc in b".
"use" directive refers to undeclared name: type "Z" is not declared in package "cc".
Error 7 WellFormedness
""", Map.of("cc", cA), Map.of("a", "cc"), """
use a.Z as Z;
B:{}
"""); }
  @Test void useOfAMapTarget(){ fail("""
In file: [###].fear

001| use c.A as X;
   |     ^^^

While inspecting package header
"use" directive refers to package "c", which is written "a" in package "b" because of "map a as c in b".
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use c.A as X;
B:{.m(x:X):X->x.fromC}
"""); }
  @Test void aliasedTypeWrittenQualified(){ fail("""
In file: [###].fear

002| B:{.m(x:X):c.A->x.fromC}
   |            ^^^^

While inspecting a type name
Type "c.A" is written "X" in package "b", because of "use c.A as X".
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of(), """
use c.A as X;
B:{.m(x:X):c.A->x.fromC}
"""); }
  @Test void aliasedTypeWrittenThroughAMap(){ fail("""
In file: [###].fear

002| B:{.m(x:X):a.A->x.fromC}
   |            ^^^^

While inspecting a type name
Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".
Type "a.A" is written "X" in package "b", because of "use a.A as X".
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:X):a.A->x.fromC}
"""); }
  @Test void useThroughMapFail(){ fail("""
In file: [###].fear

002| B:{.m(x:A):A->x.fromA}
   |    -----------~^^^^^^^

While inspecting ".m(_)" line 2
This call to method ".fromA" cannot typecheck.
Method ".fromA" is not declared on type "A".

Available methods on type "A":
-       .fromC:A

Name "A" stands for "a.A" because of "use a.A as A".
Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as A;
B:{.m(x:A):A->x.fromA}
"""); }
  @Test void useWithoutMapFailHasNoNote(){ fail("""
In file: [###].fear

002| B:{.m(x:X):X->x.fromA}
   |    -----------~^^^^^^^

While inspecting ".m(_)" line 2
This call to method ".fromA" cannot typecheck.
Method ".fromA" is not declared on type "X".

Available methods on type "X":
-       .fromC:X

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""", Map.of("c", cA), Map.of(), """
use c.A as X;
B:{.m(x:X):X->x.fromA}
"""); }
  @Test void useOfOtherPackageOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "X" stands for "c.A" because of "use c.A as X".
Name "A" is not declared with 1 type parameter in package "c".
Name "A" is only declared with 0 type parameters.
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of("c", cA), Map.of(), """
use c.A as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void useThroughMapOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "X" stands for "a.A" because of "use a.A as X".
Type name "a.A" in package "b" is mapped to the real source location "c.A" because of "map a as c in b".
Name "A" is not declared with 1 type parameter in package "c".
Name "A" is only declared with 0 type parameters.
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void twoVersionsOfAPackageMappedFromTwoNames(){ ok(Map.of("webserver_v12", "Server:{.v12:Server->this}", "webserver_v13", "Server:{.v13:Server->this}"), Map.of("old", "webserver_v12", "webserver", "webserver_v13"), """
B:{.m(x:old.Server, y:webserver.Server):webserver.Server->y.v13; .k(x:old.Server):old.Server->x.v12}
"""); }
  @Test void versionedPackageWrittenByItsRealName(){ fail("""
In file: [###].fear

001| B:{.m(x:webserver_v12.Server):webserver.Server->x.v12}
   |         ^^^^^^^^^^^^^^^^^^^^^

While inspecting a type name
Type "webserver_v12.Server" is written "webserver.Server" in package "b", because of "map webserver as webserver_v12 in b".
In a package, each name refers to a single package or type, and each package or type has a single name.
Error 7 WellFormedness
""", Map.of("webserver_v12", "Server:{.v12:Server->this}"), Map.of("webserver", "webserver_v12"), """
B:{.m(x:webserver_v12.Server):webserver.Server->x.v12}
"""); }
}