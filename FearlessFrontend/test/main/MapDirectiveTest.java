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
    var res= okOrPrint(o, () -> new FrontendLogicMain().of("b", writtenIn(map), o.allFiles(), other));
    if (!checkCompact){ return; }
    coreCmp(lines(res), compact.Print.lines(compactB(pkgs, map, o)));
  }
  static void fail(String expected, Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var fe= assertThrows(FearlessException.class, () -> new FrontendLogicMain().of("b", writtenIn(map), o.allFiles(), other));
    strCmp(expected, fe.render(o));
    if (!checkCompact){ return; }
    assertThrows(compact.Frontend.Fail.class, () -> compactB(pkgs, map, o));
  }
  static Map<String,String> writtenIn(Map<String,String> map){
    return map.entrySet().stream().collect(java.util.stream.Collectors.toMap(Map.Entry::getKey, e -> e.getValue()+" fear:/_b/_rank_app.fear"));
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

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

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

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

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

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness""", Map.of("c", "A:{.m:A->this} A2:{.m:A2->this}"), Map.of("a", "c"), """
B:a.A,a.A2{}
"""); }
  @Test void mapToMissingTypeSuggestsNoNameTheMapRedirects(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):B->this}
   |         ^^^^

While inspecting a type name
Type "A" is not declared in package "a".
In scope: "a.C".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
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
Source code inside folders named "_b" can not use package name "c".
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.A):c.A->x.fromC}
"""); }
  @Test void useOfTheCurrentPackage(){ fail("""
In file: [###].fear

001| use b.B as X;
   |     ^^^

While inspecting package header
"use" directive refers to type "B" declared inside folders named "_b".
A "use" directive can only refer to types declared in other folders.
Source code inside folders named "_b" uses the simple names of its own types.
Error 7 WellFormedness""", Map.of(), Map.of(), """
use b.B as X;
B:{.m(x:X):B->x.self; .self:X->this}
"""); }
  @Test void currentPackageQualified(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
The full type name "b.B" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "B" to refer to "b.B".
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.B):B->this}
"""); }
  @Test void currentPackageQualifiedUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:b.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "Z" is not declared in package "b".
In scope: "B".
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.Z):B->this}
"""); }
  @Test void currentPackageQualifiedOtherArity(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B[B]):B->this}
   |         ^^^^

While inspecting a type name
Name "B" is not declared with 1 type parameter in package "b".
Name "B" is only declared with 0 type parameters.
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.B[B]):B->this}
"""); }
  @Test void mapTargetQualifiedUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:c.Z):B->this}
   |         ^^^^

While inspecting a type name
Source code inside folders named "_b" can not use package name "c".
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:c.Z):B->this}
"""); }
  @Test void currentPackageQualifiedWithOtherOptions(){ fail("""
In file: [###].fear

002| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
The full type name "b.B" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "B" to refer to "b.B".
Did you mean "a.B" or "d.B" ?

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "B:{}", "d", "B:{}", "e", "B:{}"), Map.of("a", "c"), """
use e.B as EB;
B:{.m(x:b.B):B->this}
"""); }
  @Test void useOfAMissingPackage(){ fail("""
In file: [###].fear

001| use zz.A as X;
   |     ^^^^

While inspecting package header
Source code inside folders named "_b" can not use package name "zz".
Visible package names: "base".
Error 7 WellFormedness
""", Map.of(), Map.of(), """
use zz.A as X;
B:{}
"""); }
  @Test void mapToMissingType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "Z" is not declared in package "a".
In scope: "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
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
"use" directive refers to type "Z", which is not declared in package "a".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_cc", because of "map a as _cc in _b", written in fear:/_b/_rank_app.fear.
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
Source code inside folders named "_b" can not use package name "c".
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
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
The full type name "c.A" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "X" to refer to "c.A", because of "use c.A as X".
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
The full type name "a.A" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "X" to refer to "a.A", because of "use a.A as X".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
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
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

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
Name "A" is not declared with 1 type parameter in package "c".
Name "A" is only declared with 0 type parameters.
Did you accidentally add or omit a type parameter?

Name "X" stands for "c.A" because of "use c.A as X".
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
Name "A" is not declared with 1 type parameter in package "a".
Name "A" is only declared with 0 type parameters.
Did you accidentally add or omit a type parameter?

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
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
Source code inside folders named "_b" can not use package name "webserver_v12".
Did you mean "webserver" ?
Visible package names: "base", "webserver".
Source code inside folders named "_b" uses package name "webserver" to refer to the code inside folders named "_webserver_v12", because of "map webserver as _webserver_v12 in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("webserver_v12", "Server:{.v12:Server->this}"), Map.of("webserver", "webserver_v12"), """
B:{.m(x:webserver_v12.Server):webserver.Server->x.v12}
"""); }
  static final String pq= "P:{ .x:P->this; .y:P->this; }\n";
  @Test void destructuringWithAnAliasForDestruct(){ ok(Map.of(), Map.of(), """
use base.Destruct as D;
"""+pq+"""
B:{ .m({.x, .y}:P):P -> x }
"""); }
  @Test void destructuringWithBaseReachedThroughAMap(){ ok(Map.of(), Map.of("bb", "base"), pq+"""
B:{ .m({.x, .y}:P):P -> y }
"""); }
  @Test void destructuringWithBaseReachedThroughAMapAndAnAliasForDestruct(){ ok(Map.of(), Map.of("bb", "base"), """
use bb.Destruct as D;
"""+pq+"""
B:{ .m({.x, .y}:P):P -> x; .k(d:D):D -> d }
"""); }
  @Test void destructuringNextToADeclaredTypeNamedDestruct(){ ok(Map.of(), Map.of(), pq+"""
Destruct:{}
B:{ .m({.x, .y}:P):P -> x; .k(d:Destruct):Destruct -> d }
"""); }
  @Test void baseTypesThroughAMapAndAnAlias(){ ok(Map.of(), Map.of("bb", "base"), """
use bb.Str as S;
B:{ .m(x:S):S -> x; .v:bb.Void -> {} }
"""); }
  @Test void aliasAndQualifiedNamesThroughTheSameMap(){ ok(Map.of("c", "A:{} A2:{}"), Map.of("a", "c"), """
use a.A as X;
B:{ .m(x:X):X -> x; .k(y:a.A2):a.A2 -> y }
"""); }
  @Test void baseByItsRealNameWhenAMapRenamesIt(){ fail("""
In file: [###].fear

001| B:{ .v:base.Void -> {} }
   |        ^^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" can not use package name "base".
Visible package names: "bb".
Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
B:{ .v:base.Void -> {} }
"""); }
  @Test void numberWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:B -> 5 }
   |     --------^

While inspecting object literal instance of "bb.Nat" > ".m" line 1
The body of method ".m" of type declaration "B" is an expression returning "iso bb.Nat".
Object literal is of type "bb.Nat" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m:B->5}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
B:{ .m:B -> 5 }
"""); }
  @Test void methodOfANumberWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:B -> 5.foo }
   |     --------~^^^^

While inspecting ".m" line 1
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on type "bb.Nat".

Available methods on type "bb.Nat":
-       *(bb.Nat):bb.Nat
-       +(bb.Nat):bb.Nat

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
5.foo
Error 8 TypeError""",Map.of(), Map.of("bb", "base"), """
B:{ .m:B -> 5.foo }
"""); }
  static final String sealedC= "S:base.Sealed{ .m:S }";
  @Test void sealedTypeThroughAMap(){ fail("""
In file: [###].fear

001| B:a.S{ .m -> this }
   | ^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements sealed type "a.S".
Sealed types can only be implemented in their own package.
Type declaration "B" is defined in package "b".
Type "S" is defined in package "a".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", sealedC), Map.of("a", "c"), """
B:a.S{ .m -> this }
"""); }
  @Test void sealedTypeThroughAMapAndAnAlias(){ fail("""
In file: [###].fear

002| B:X{ .m -> this }
   | ^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type declaration "B" implements sealed type "X".
Sealed types can only be implemented in their own package.
Type declaration "B" is defined in package "b".
Type "S" is defined in package "a".

Name "X" stands for "a.S" because of "use a.S as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", sealedC), Map.of("a", "c"), """
use a.S as X;
B:X{ .m -> this }
"""); }
  @Test void sealedTypeUsedAsAnExpressionThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .k:a.S -> a.S }
   |     ----------^^^

While inspecting object literal instance of "iso a.S" > ".k" line 1
This object literal is missing a required method.
Missing: "imm .m".
Required by: "a.S".
Sealed types can only be implemented in their own package.
Type "S" is defined in package "a".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso -.S
Error 8 TypeError""",Map.of("c", sealedC), Map.of("a", "c"), """
B:{ .k:a.S -> a.S }
"""); }
  @Test void undeclaredSimpleNameSuggestsTheMappedName(){ fail("""
In file: [###].fear

001| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "a.Server" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}"), Map.of("a", "c"), """
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsTheAlias(){ fail("""
In file: [###].fear

002| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B", "Remote".
Did you mean "Remote" ?

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredQualifiedNameSuggestsTheAlias(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Serve):B->this}
   |         ^^^^^^^^

While inspecting a type name
Type "Serve" is not declared in package "a".
Did you mean "Remote" ?
In scope: "Remote".

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:a.Serve):B->this}
"""); }
  @Test void undeclaredQualifiedNameListsTheAliasInScope(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Type "Z" is not declared in package "a".
In scope: "X".

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Z):B->this}
"""); }
  @Test void wrongPackageSuggestsTheAliasOfTheSameSimpleName(){ fail("""
In file: [###].fear

002| B:{.m(x:d.Server):B->this}
   |         ^^^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "d".
In scope: "d.Client".
Did you mean "Remote" ?

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}", "d", "Client:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:d.Server):B->this}
"""); }
  @Test void wrongPackageSuggestsTheOwnSimpleName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Server):B->this}
   |         ^^^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "a".
In scope: "a.A".
Did you mean "Server" ?

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
B:{.m(x:a.Server):B->this}
Server:{}
"""); }
  @Test void wrongPackageSuggestsTheMappedName(){ fail("""
In file: [###].fear

001| B:{.m(x:d.Server):B->this}
   |         ^^^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "d".
In scope: "d.Client".
Did you mean "a.Server" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}", "d", "Client:{}"), Map.of("a", "c"), """
B:{.m(x:d.Server):B->this}
"""); }
  static final String cBox= "A:{.fromC:A->this} D:{} Box[T]:{.get:T; .put(t:T):Box[T]->this}";
  @Test void callResultWithAMappedTypeArgument(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[a.A]):B->x.get}
   |    --------------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "a.A".
Method call "a.Box[_].get" has type "a.A" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.Box[-.A]):B->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[a.A]):B->x.get}
"""); }
  @Test void callResultWithAnOwnTypeAsTheArgumentOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[B]):a.A->x.get}
   |    --------------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "B".
Method call "a.Box[_].get" has type "B" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m(x:-.Box[B]):-.A->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[B]):a.A->x.get}
"""); }
  @Test void callResultWithAnAliasAsTheArgumentOfAMappedType(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Box[X]):B->x.get}
   |    ------------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "B" is an expression returning "X".
Method call "a.Box[_].get" has type "X" instead of a subtype of "B".

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.Box[X]):B->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[X]):B->x.get}
"""); }
  @Test void callResultWithTwoAliasesThroughTheSameMap(){ fail("""
In file: [###].fear

003| B:{.m(x:Bx[X]):B->x.get}
   |    ---------------^^^^^^

While inspecting method call ".get" > ".m(_)" line 3
The body of method ".m(_)" of type declaration "B" is an expression returning "X".
Method call "Bx[_].get" has type "X" instead of a subtype of "B".

Name "X" stands for "a.A" because of "use a.A as X".
Name "Bx" stands for "a.Box" because of "use a.Box as Bx".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:Bx[X]):B->x.get}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.Box as Bx;
use a.A as X;
B:{.m(x:Bx[X]):B->x.get}
"""); }
  @Test void aliasedTypeWrittenQualifiedAsATypeArgument(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Box[a.A]):B->this}
   |               ^^^^

While inspecting a type name
The full type name "a.A" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "X" to refer to "a.A", because of "use a.A as X".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[a.A]):B->this}
"""); }
  @Test void mapTargetWrittenAsATypeArgument(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[c.A]):B->this}
   |               ^^^^

While inspecting a type name
Source code inside folders named "_b" can not use package name "c".
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[c.A]):B->this}
"""); }
  @Test void mappedGenericTypesWithAliasesAndOwnTypes(){ ok(Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[X]):X->x.get.fromC; .k(y:a.Box[X], z:X):a.Box[X]->y.put(z); .own(b:a.Box[B]):B->b.get}
"""); }
  static final Map<String,String> webVersions= Map.of("web_v1", "Server:{.v1:Server->this}", "web_v2", "Server:{.v2:Server->this}");
  static final Map<String,String> legacyAndWeb= Map.of("legacy", "web_v1", "web", "web_v2");
  @Test void anAliasAndAMapForTwoVersionsOfAPackage(){ ok(webVersions, legacyAndWeb, """
use legacy.Server as OldServer;
B:{.m(x:OldServer, y:web.Server):web.Server->y.v2; .k(x:OldServer):OldServer->x.v1}
"""); }
  @Test void anAliasAndAMapForTwoVersionsDisagree(){ fail("""
In file: [###].fear

002| B:{.m(x:OldServer):web.Server->x}
   |    ----------------------------^^

While inspecting parameter "x" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "B" is an expression returning "OldServer".
Parameter "x" has type "OldServer" instead of a subtype of "web.Server".

Name "OldServer" stands for "legacy.Server" because of "use legacy.Server as OldServer".
Source code inside folders named "_b" uses package name "legacy" to refer to the code inside folders named "_web_v1", because of "map legacy as _web_v1 in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "web" to refer to the code inside folders named "_web_v2", because of "map web as _web_v2 in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "web.Server" was introduced: (compression indicated by `-`)
B:{.m(x:OldServer):-.Server->x}
Error 8 TypeError""", webVersions, legacyAndWeb, """
use legacy.Server as OldServer;
B:{.m(x:OldServer):web.Server->x}
"""); }
  @Test void aMethodOfTheOtherVersionThroughAnAlias(){ fail("""
In file: [###].fear

002| B:{.m(x:OldServer, y:web.Server):web.Server->x.v2}
   |    ------------------------------------------~^^^^

While inspecting ".m(_,_)" line 2
This call to method ".v2" cannot typecheck.
Method ".v2" is not declared on type "OldServer".
Did you mean ".v1" ?

Available methods on type "OldServer":
-       .v1:OldServer

Name "OldServer" stands for "legacy.Server" because of "use legacy.Server as OldServer".
Source code inside folders named "_b" uses package name "legacy" to refer to the code inside folders named "_web_v1", because of "map legacy as _web_v1 in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.v2
Error 8 TypeError""", webVersions, legacyAndWeb, """
use legacy.Server as OldServer;
B:{.m(x:OldServer, y:web.Server):web.Server->x.v2}
"""); }
  @Test void methodNotDeclaredOnAQualifiedMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):a.A->x.nope}
   |    ---------------~^^^^^^

While inspecting ".m(_)" line 1
This call to method ".nope" cannot typecheck.
Method ".nope" is not declared on type "a.A".

Available methods on type "a.A":
-       .fromC:a.A

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.nope
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.A):a.A->x.nope}
"""); }
  @Test void readMappedTypeWhereMutIsRequired(){ fail("""
In file: [###].fear

001| B:{.m(x:read a.A):mut a.A->x}
   |    ------------------------^^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "read a.A".
Parameter "x" has type "read a.A" instead of a subtype of "mut a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "mut a.A" was introduced: (compression indicated by `-`)
B:{.m(x:read -.A):mut -.A->x}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:read a.A):mut a.A->x}
"""); }
  @Test void mutAndReadMappedTypes(){ ok(Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.k(x:mut X):read X->x; .j(x:mut a.Box[X]):read a.Box[X]->x; .d(x:mut a.D):read a.D->x}
"""); }
  @Test void argumentOfTheWrongMappedType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Box[a.A], d:a.D):a.Box[a.A]->x.put(d)}
   |    ------------------------------------~^^^^^~~

While inspecting ".m(_,_)" line 1
This call to method "a.Box[_].put(_)" cannot typecheck.
Argument 1 has type "a.D".
That is not a subtype of "a.A" (the type required by the method signature).

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
-.put(d)
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m(x:a.Box[a.A], d:a.D):a.Box[a.A]->x.put(d)}
"""); }
  @Test void argumentOfTheWrongAliasedType(){ fail("""
In file: [###].fear

002| B:{.m(x:a.Box[X], d:a.D):a.Box[X]->x.put(d)}
   |    --------------------------------~^^^^^~~

While inspecting ".m(_,_)" line 2
This call to method "a.Box[_].put(_)" cannot typecheck.
Argument 1 has type "a.D".
That is not a subtype of "X" (the type required by the method signature).

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
-.put(d)
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:a.Box[X], d:a.D):a.Box[X]->x.put(d)}
"""); }
  @Test void nestedObjectLiteralOfAMappedType(){ fail("""
In file: [###].fear

001| B:{.m:a.A->a.A{.fromC->base.Void}}
   |    ------------~~~~~~~~^^^^^^^^^^

While inspecting object literal instance of "base.Void" > ".fromC" line 1 > ".m" line 1
Method ".fromC" inside the object literal instance of "iso a.A" (line 1)
is implemented with an expression returning "iso base.Void".
Object literal is of type "base.Void" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m:-.A->-.A{.fromC:-.A->-.Void}}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m:a.A->a.A{.fromC->base.Void}}
"""); }
  @Test void literalMissingTheMethodOfAMappedGenericType(){ fail("""
In file: [###].fear

001| B:{.m:a.Box[a.A]->{}}
   |    ---------------^^

While inspecting object literal instance of "iso a.Box[a.A]" > ".m" line 1
This object literal is missing a required method.
Missing: "imm .get".
Required by: "a.Box[_]".
Hint: add an implementation for ".get" inside the object literal.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso -.Box[-.A]
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
B:{.m:a.Box[a.A]->{}}
"""); }
  @Test void stringWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:B -> "hi" }
   |     --------^^^^

While inspecting object literal instance of "bb.Str" > ".m" line 1
The body of method ".m" of type declaration "B" is an expression returning "iso bb.Str".
Object literal is of type "bb.Str" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m:B->"hi"}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
B:{ .m:B -> "hi" }
"""); }
  @Test void numberWithAnAliasForNatThroughAMap(){ fail("""
In file: [###].fear

002| B:{ .m:B -> 5 }
   |     --------^

While inspecting object literal instance of "N" > ".m" line 2
The body of method ".m" of type declaration "B" is an expression returning "iso N".
Object literal is of type "N" instead of a subtype of "B".

Name "N" stands for "bb.Nat" because of "use bb.Nat as N".
Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m:B->5}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
use bb.Nat as N;
B:{ .m:B -> 5 }
"""); }
  @Test void signedNumberWithBaseReachedThroughAMap(){ fail("""
In file: [###].fear

001| B:{ .m:bb.Nat -> +5 }
   |     -------------^^

While inspecting object literal instance of "bb.Int" > ".m" line 1
The body of method ".m" of type declaration "B" is an expression returning "iso bb.Int".
Object literal is of type "bb.Int" instead of a subtype of "bb.Nat".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "bb.Nat" was introduced: (compression indicated by `-`)
B:{.m:-.Nat->+5}
Error 8 TypeError""", Map.of(), Map.of("bb", "base"), """
B:{ .m:bb.Nat -> +5 }
"""); }
  @Test void ownTypeAndMappedTypeWithTheSameSimpleName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.B):B->x}
   |    -------------^^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "a.B".
Parameter "x" has type "a.B" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.B):B->x}
Error 8 TypeError""", Map.of("c", "B:{.fromC:B->this}"), Map.of("a", "c"), """
B:{.m(x:a.B):B->x}
"""); }
  @Test void baseTypeInTheSignatureOfAMappedPackageWhenBaseIsMappedToo(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):B->x.n}
   |    -------------^^^^

While inspecting method call ".n" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "bb.Nat".
Method call "a.A.n" has type "bb.Nat" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "bb" to refer to the code inside folders named "_base", because of "map bb as _base in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.A):B->x.n}
Error 8 TypeError""", Map.of("c", "A:{.n:base.Nat->5}"), Map.of("a", "c", "bb", "base"), """
B:{.m(x:a.A):B->x.n}
"""); }
  @Test void genericMethodCalledWithAMappedTypeArgument(){ fail("""
In file: [###].fear

001| B:{.m(x:a.G, d:a.D):B->x.id[a.D](d)}
   |    --------------------^^^^^^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 1
The body of method ".m(_,_)" of type declaration "B" is an expression returning "a.D".
Method call "a.G.id(_)" has type "a.D" instead of a subtype of "B".

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
B:{.m(x:-.G,d:-.D):B->x.id[imm,-.D](d)}
Error 8 TypeError""", Map.of("c", "D:{} G:{.id[X](x:X):X->x}"), Map.of("a", "c"), """
B:{.m(x:a.G, d:a.D):B->x.id[a.D](d)}
"""); }
  @Test void genericMethodCalledWithAMappedTypeArgumentAndAnAlias(){ ok(Map.of("c", "D:{} G:{.id[X](x:X):X->x}"), Map.of("a", "c"), """
use a.D as Dd;
B:{.m(x:a.G, d:Dd):Dd->x.id[Dd](d); .k(x:a.G, d:Dd):Dd->x.id(d)}
"""); }
  @Test void nestedObjectLiteralOfAnAlias(){ fail("""
In file: [###].fear

002| B:{.m:X->X{.fromC->B}}
   |    --------~~~~~~~~^^

While inspecting object literal instance of "B" > ".fromC" line 2 > ".m" line 2
Method ".fromC" inside the object literal instance of "iso X" (line 2)
is implemented with an expression returning "iso B".
Object literal is of type "B" instead of a subtype of "X".

Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c", because of "map a as _c in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.m:X->X{.fromC:X->B}}
Error 8 TypeError""", Map.of("c", cBox), Map.of("a", "c"), """
use a.A as X;
B:{.m:X->X{.fromC->B}}
"""); }
  @Test void literalsWithBaseReachedThroughAMapAndAliases(){ ok(Map.of(), Map.of("bb", "base"), """
use bb.Nat as N;
use bb.Str as S;
B:{ .m:N -> 5; .k(x:N):N -> x+5; .s:S -> "hi"; .i:bb.Int -> +5; .f:bb.Float -> 1.5 }
"""); }
  static final String noteA= "Source code inside folders named \"_b\" uses package name \"a\" to refer to the code inside folders named \"_c\", because of \"map a as _c in _b\", written in fear:/_b/_rank_app.fear.";
  static final String noteBb= "Source code inside folders named \"_b\" uses package name \"bb\" to refer to the code inside folders named \"_base\", because of \"map bb as _base in _b\", written in fear:/_b/_rank_app.fear.";
  @Test void undeclaredSimpleNameSuggestsAnAliasOfAnUnmappedTypeWithNoNote(){ fail("""
In file: [###].fear

002| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B", "Remote".
Did you mean "Remote" ?
Error 7 WellFormedness
""", Map.of("c", cA, "d", "Server:{}"), Map.of("a", "c"), """
use d.Server as Remote;
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsAnAliasAndAnUnmappedName(){ fail("""
In file: [###].fear

002| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B", "Remote".
Did you mean "Remote" or "d.Server" ?
Add a "use" or write the full type name.

Name "Remote" stands for "a.Server" because of "use a.Server as Remote".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "Server:{}", "d", "Server:{}"), Map.of("a", "c"), """
use a.Server as Remote;
B:{.m(x:Server):B->this}
"""); }
  @Test void undeclaredSimpleNameListsAMappedAliasInScope(){ fail("""
In file: [###].fear

002| B:{.m(x:Qqqqqq):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Qqqqqq" is not declared in package "b" and is not made visible via "use".
In scope: "B", "X".

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use a.A as X;
B:{.m(x:Qqqqqq):B->this}
"""); }
  @Test void undeclaredQualifiedNameInAMappedBaseSuggestsTheBaseType(){ fail("""
In file: [###].fear

001| B:{.m(x:bb.Strr):B->this}
   |         ^^^^^^^^

While inspecting a type name
Type "Strr" is not declared in package "bb".
Did you mean "bb.Str" ?

"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
B:{.m(x:bb.Strr):B->this}
"""); }
  @Test void undeclaredQualifiedNameInAMappedBaseSuggestsTheAliasOfTheBaseType(){ fail("""
In file: [###].fear

002| B:{.m(x:bb.Strr):B->this}
   |         ^^^^^^^^

While inspecting a type name
Type "Strr" is not declared in package "bb".
Did you mean "S" ?

Name "S" stands for "bb.Str" because of "use bb.Str as S".
"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
use bb.Str as S;
B:{.m(x:bb.Strr):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsABaseTypeThroughAMap(){ fail("""
In file: [###].fear

001| B:{.m(x:Str):B->this}
   |         ^^^^

While inspecting a type name
Type "Str" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "bb.Str" ?
Add a "use" or write the full type name.

"""+noteBb+"""

Error 7 WellFormedness
""", Map.of(), Map.of("bb", "base"), """
B:{.m(x:Str):B->this}
"""); }
  @Test void undeclaredSimpleNameSuggestsTwoMappedNamesWithTheirNotesInTheOrderShown(){ fail("""
In file: [###].fear

001| B:{.m(x:Server):B->this}
   |         ^^^^^^^

While inspecting a type name
Type "Server" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "a.Server" or "z.Server" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_e", because of "map a as _e in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_c", because of "map z as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", "Server:{}", "e", "Server:{}"), Map.of("z", "c", "a", "e"), """
B:{.m(x:Server):B->this}
"""); }
  @Test void currentPackageQualifiedSuggestsAMappedNameWithItsNote(){ fail("""
In file: [###].fear

001| B:{.m(x:b.B):B->this}
   |         ^^^^

While inspecting a type name
The full type name "b.B" is invalid in source code inside folders named "_b".
Source code inside folders named "_b" uses the simple name "B" to refer to "b.B".
Did you mean "a.B" ?

"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "B:{}"), Map.of("a", "c"), """
B:{.m(x:b.B):B->this}
"""); }
  @Test void missingReturnTypeInALiteralOfAMappedTypeNamesTheMapOnlyInTheFrame(){ fail("""
In file: [###].fear

001| B:{ .m:a.A->{ .k->B; }; }
   |             --^^^^^---

While inspecting object literal instance of "a.A"
Missing return type for method ".k".
Add an explicit return type before '->'.
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".k".
No supertype has a method named ".k" with 0 parameters.

"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "A:{}"), Map.of("a", "c"), """
B:{ .m:a.A->{ .k->B; }; }
"""); }
  @Test void missingReturnTypeInALiteralOfAMappedAliasNamesTheAliasOnlyInTheFrame(){ fail("""
In file: [###].fear

002| B:{ .m:X->{ .k->B; }; }
   |           --^^^^^---

While inspecting object literal instance of "X"
Missing return type for method ".k".
Add an explicit return type before '->'.
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".k".
No supertype has a method named ".k" with 0 parameters.

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""

Error 7 WellFormedness
""", Map.of("c", "A:{}"), Map.of("a", "c"), """
use a.A as X;
B:{ .m:X->{ .k->B; }; }
"""); }
  static final String cIds= "IdRO:{ #[X:imm,read](x:X):X->x } Id:{ #[X:**](x:X):X->x }";
  @Test void argumentMatchingNoPromotionNamesAMappedReceiverOnlyInTheReason(){ fail("""
In file: [###].fear

003| A:{ .f(aaaa:mut A):B->Need#(a.IdRO#[read A](aaaa)); }
   |     ------------------~~~~^^~~~~~~~~~~~~~~~~~~~~~-

While inspecting ".f(_)" line 3
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "a.IdRO#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

"""+noteA+"""


See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):B->Need#(-.IdRO#[imm,read A](aaaa))}
Error 8 TypeError""", Map.of("c", cIds), Map.of("a", "c"), """
B:{}
Need:{ #(x:mut A):B->B{} }
A:{ .f(aaaa:mut A):B->Need#(a.IdRO#[read A](aaaa)); }
"""); }
  @Test void argumentMatchingNoPromotionNamesAMappedAliasOnlyInTheReason(){ fail("""
In file: [###].fear

004| A:{ .f(aaaa:mut A):B->Need#(Ro#[read A](aaaa)); }
   |     ------------------~~~~^^~~~~~~~~~~~~~~~~~-

While inspecting ".f(_)" line 4
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "Ro#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

Name "Ro" stands for "a.IdRO" because of "use a.IdRO as Ro".
"""+noteA+"""


See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):B->Need#(Ro#[imm,read A](aaaa))}
Error 8 TypeError""", Map.of("c", cIds), Map.of("a", "c"), """
use a.IdRO as Ro;
B:{}
Need:{ #(x:mut A):B->B{} }
A:{ .f(aaaa:mut A):B->Need#(Ro#[read A](aaaa)); }
"""); }
  @Test void promotionsDisagreeNameAMappedReceiverOnlyInThePromotionFailures(){ fail("""
In file: [###].fear

001| A:{ .f(p:read A, q:mut A):A->this; .caller(x:readH A, y:mutH A):A->this.f(a.Id#(x), y); }
   |                                    --------------------------------~~~~^^^~~~~~~~~~~~~

While inspecting ".caller(_,_)" line 1
This call to method ".f(_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Method call "a.Id#(_)" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Method call "a.Id#(_)" has type "readH A" instead of a subtype of "A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

"""+noteA+"""


Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(-.Id#[imm,read A](x),y)
Error 8 TypeError""", Map.of("c", cIds), Map.of("a", "c"), """
A:{ .f(p:read A, q:mut A):A->this; .caller(x:readH A, y:mutH A):A->this.f(a.Id#(x), y); }
"""); }
  @Test void twoMapsInOneTypeErrorGiveTwoNotesInTheOrderTheNamesArePrinted(){ fail("""
In file: [###].fear

001| B:{.m(x:z.A):a.A->x}
   |    ---------------^^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "B" is an expression returning "z.A".
Parameter "x" has type "z.A" instead of a subtype of "a.A".

Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_c", because of "map z as _c in _b", written in fear:/_b/_rank_app.fear.
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_e", because of "map a as _e in _b", written in fear:/_b/_rank_app.fear.

See inferred typing context below for how type "a.A" was introduced: (compression indicated by `-`)
B:{.m(x:-.A):-.A->x}
Error 8 TypeError""", Map.of("c", cA, "e", aA), Map.of("z", "c", "a", "e"), """
B:{.m(x:z.A):a.A->x}
"""); }
  @Test void aliasesOfAMappedAndOfAnUnmappedTypeNoteOnlyTheMappedOne(){ fail("""
In file: [###].fear

003| B:{.m(x:Dd):X->x}
   |    ------------^^

While inspecting parameter "x" > ".m(_)" line 3
The body of method ".m(_)" of type declaration "B" is an expression returning "Dd".
Parameter "x" has type "Dd" instead of a subtype of "X".

Name "X" stands for "a.A" because of "use a.A as X".
"""+noteA+"""


See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.m(x:Dd):X->x}
Error 8 TypeError""", Map.of("c", cA, "d", dA), Map.of("a", "c"), """
use d.A as Dd;
use a.A as X;
B:{.m(x:Dd):X->x}
"""); }
  @Test void twoAliasesThroughTwoMapsGiveTheNameNotesFirst(){ fail("""
In file: [###].fear

003| B:{.m(x:Y):X->x}
   |    -----------^^

While inspecting parameter "x" > ".m(_)" line 3
The body of method ".m(_)" of type declaration "B" is an expression returning "Y".
Parameter "x" has type "Y" instead of a subtype of "X".

Name "Y" stands for "z.A" because of "use z.A as Y".
Name "X" stands for "a.A" because of "use a.A as X".
Source code inside folders named "_b" uses package name "z" to refer to the code inside folders named "_e", because of "map z as _e in _b", written in fear:/_b/_rank_app.fear.
"""+noteA+"""


See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
B:{.m(x:Y):X->x}
Error 8 TypeError""", Map.of("c", cA, "e", dA), Map.of("a", "c", "z", "e"), """
use a.A as X;
use z.A as Y;
B:{.m(x:Y):X->x}
"""); }
  @Test void packageNamesAsAndInThroughMaps(){ ok(Map.of("c", cA, "d", dA), Map.of("as", "c", "in", "d"), """
map as as _c in _b;
map in as _d in _b;
B:{.m(x:as.A, y:in.A):as.A->x.fromC; .n(y:in.A):in.A->y.fromD}
"""); }
  @Test void packageNamesInsteadAndOfThroughMapsWithAnInsteadOfList(){ ok(Map.of("c", cA, "d", dA), Map.of("instead", "c", "of", "d"), """
map instead as _c in _b instead of _instead, _of;
map of as _d in _b instead of _instead;
use of.A as OfA;
B:{.m(x:instead.A, y:OfA):OfA->y.fromD}
"""); }
  @Test void packageNamesMapAndUseThroughMaps(){ ok(Map.of("c", cA, "d", dA), Map.of("map", "c", "use", "d"), """
map map as _c in _b;
map use as _d in _b;
use map.A as M;
B:{.m(x:M, y:use.A):use.A->y.fromD; .k(x:M):M->x.fromC}
"""); }
  @Test void aParameterNamedLikeTheMappedPackage(){ ok(Map.of("c", cA), Map.of("a", "c"), """
B:{.m(a:a.A):a.A->a.fromC; .k(as:a.A):a.A->as.fromC}
"""); }
  @Test void aFolderNameWithExtraUnderscores(){ ok(Map.of("c__v_", cA), Map.of("a", "c__v_"), """
map a as _c__v_ in _b instead of _c__v4_;
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void aFolderNameWithExtraUnderscoresWrittenByItsOwnName(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):c__v_.A->x.fromC}
   |              ^^^^^^^^

While inspecting a type name
Source code inside folders named "_b" can not use package name "c__v_".
Visible package names: "a", "base".
Source code inside folders named "_b" uses package name "a" to refer to the code inside folders named "_c__v_", because of "map a as _c__v_ in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c__v_", cA), Map.of("a", "c__v_"), """
B:{.m(x:a.A):c__v_.A->x.fromC}
"""); }
  @Test void aKeywordLikeMapTargetWrittenByItsOwnName(){ fail("""
In file: [###].fear

001| B:{.m(x:as.A):in.A->x.fromC}
   |               ^^^^^

While inspecting a type name
Source code inside folders named "_b" can not use package name "in".
Visible package names: "as", "base".
Source code inside folders named "_b" uses package name "as" to refer to the code inside folders named "_in", because of "map as as _in in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("in", cA), Map.of("as", "in"), """
B:{.m(x:as.A):in.A->x.fromC}
"""); }
  @Test void useOfAKeywordLikeMappedNameToAMissingType(){ fail("""
In file: [###].fear

001| use of.Z as Z;
   |     ^^^^

While inspecting package header
"use" directive refers to type "Z", which is not declared in package "of".

Source code inside folders named "_b" uses package name "of" to refer to the code inside folders named "_c", because of "map of as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("of", "c"), """
use of.Z as Z;
B:{}
"""); }
  @Test void useOfASimpleNameNextToAMap(){ fail("""
In file: [###].fear

001| use A as X;
   |     ^

While inspecting package header
"use" directive refers to "A", which is not a full type name.
A "use" directive refers to a type of another package by its full type name, as in "use base.Str as Str;".
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("a", "c"), """
use A as X;
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void undeclaredSimpleNameThroughAKeywordLikeMap(){ fail("""
In file: [###].fear

001| B:{.m(x:A):B->this}
   |         ^^

While inspecting a type name
Type "A" is not declared in package "b" and is not made visible via "use".
In scope: "B".
Did you mean "in.A" ?
Add a "use" or write the full type name.

Source code inside folders named "_b" uses package name "in" to refer to the code inside folders named "_c", because of "map in as _c in _b", written in fear:/_b/_rank_app.fear.
Error 7 WellFormedness
""", Map.of("c", cA), Map.of("in", "c"), """
B:{.m(x:A):B->this}
"""); }
  @Test void literalsWithBaseMappedToAKeywordLikeName(){ ok(Map.of(), Map.of("in", "base"), """
B:{ .m:in.Nat -> 5; .s:in.Str -> "hi"; .i:in.Int -> +5 }
"""); }
  @Test void reservedLookingButValidNamesInAMapLine(){ ok(Map.of("c", cA), Map.of("con1", "c"), """
map con1 as _com0 in _lpt10 instead of _nul_, _aux2;
B:{.m(x:con1.A):con1.A->x.fromC}
"""); }
  @Test void aReservedFolderNameInAMapLine(){ fail("""
In file: [###].fear

001| map a as _com1 in _b;
   | ~~~~~~~~~^^^^^~~~~~~-
002| B:{}

While inspecting header element > file header > full file
Missing folder name.
Found instead: "_com1".
Expected: "folder name: the _ symbol followed by a package name".
Error 2 UnexpectedToken
""", Map.of(), Map.of(), """
map a as _com1 in _b;
B:{}
"""); }
  @Test void anInsteadOfListWithoutSpacesAndWithComments(){ ok(Map.of("c", cA), Map.of("a", "c"), """
map a as _c /*folder*/ in _b instead of _d,_e //older
  ,_f;
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void anInsteadOfListWithATrailingComma(){ fail("""
In file: [###].fear

001| map a as _c in _b instead of _d,;
   | ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^-
002| B:{}

While inspecting header element > file header > full file
Missing folder name.
Expected: "folder name: the _ symbol followed by a package name".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _c in _b instead of _d,;
B:{}
"""); }
  @Test void anInsteadOfListWithoutOf(){ fail("""
In file: [###].fear

001| map a as _c in _b instead _d;
   | ~~~~~~~~~~~~~~~~~~~~~~~~~~^^-
002| B:{}

While inspecting header element > file header > full file
Missing "of" keyword.
Found instead: "_d".
Expected: "of".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _c in _b instead _d;
B:{}
"""); }
  @Test void aMapLineWithoutItsSemicolonBeforeADeclaration(){ fail("""
In file: [###].fear

001| map a as _c in _b instead of _d
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
002| B:{}

While inspecting file header > full file
Missing semicolon.
Found instead: "_d".
Expected: ";".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _c in _b instead of _d
B:{}
"""); }
  @Test void aRepeatedMapLineWithKeywordLikeNames(){ fail("""
In file: [###].fear

001| map in as _c in _as;
002| map in as _d in _as instead of _c;
   | -------------------------------^^

While inspecting header element > file header > full file
There is already a map of package name "in" for source code inside folders named "_as".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("in", "c"), """
map in as _c in _as;
map in as _d in _as instead of _c;
B:{}
"""); }
  @Test void aMapLineWithAnUppercaseFolderName(){ fail("""
In file: [###].fear

001| map a as _cC in _b;
   | ~~~~~~~~~^^^~~~~~~-
002| B:{}

While inspecting header element > file header > full file
Missing folder name.
Found instead: "_cC".
Expected: "folder name: the _ symbol followed by a package name".
Error 2 UnexpectedToken
""", Map.of("c", cA), Map.of("a", "c"), """
map a as _cC in _b;
B:{}
"""); }
}