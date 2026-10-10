package main;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import core.AllLs;
import core.FearlessException;
import core.OtherPackages;
import testUtils.DbgBlock;

public class MapDirectiveTest extends testUtils.FearlessTestBase{
  static final String aA= "A:{.fromA:A->this}";
  static final String cA= "A:{.fromC:A->this}";
  static final String dA= "A:{.fromD:A->this}";
  static OtherPackages others(Map<String,String> pkgs){
    var res= otherFrom(DbgBlock.all());
    for (var e : pkgs.entrySet()){
      var o= oraclePkg(List.of(e.getValue()));
      var lits= compileAll(e.getKey(), o, otherFrom(DbgBlock.all()));
      res= res.mergeWith(AllLs.of(lits), -1);
    }
    return res;
  }
  static void ok(Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    okOrPrint(o, ()->new FrontendLogicMain().of("b", map, o.allFiles(), other));
  }
  static void fail(String expected, Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var fe= assertThrows(FearlessException.class, ()->new FrontendLogicMain().of("b", map, o.allFiles(), other));
    strCmp(expected, fe.render(o));
  }
  @Test void noMapQualifiedNameIsLiteral(){ ok(Map.of("a",aA,"c",cA), Map.of(), """
B:{.m(x:a.A):a.A->x.fromA}
"""); }
  @Test void mappedNameStandsForTheOutPackage(){ ok(Map.of("a",aA,"c",cA), Map.of("a","c"), """
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void mappedNameNoLongerReachesTheInPackage(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):a.A->x.fromA}
   |    ---------------~^^^^^^^

While inspecting ".m(_)" line 1
This call to method ".fromA" cannot typecheck.
Method ".fromA" is not declared on type "c.A".

Available methods on type "c.A":
-       .fromC:c.A

Name "a.A" stands for "c.A" because of "map a as c in b".

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""", Map.of("a",aA,"c",cA), Map.of("a","c"), """
B:{.m(x:a.A):a.A->x.fromA}
"""); }
  @Test void inPackageNeedNotExist(){ ok(Map.of("c",cA), Map.of("a","c"), """
B:{.m(x:a.A):a.A->x.fromC}
"""); }
  @Test void outPackageIsStillReachableByItsOwnName(){ ok(Map.of("a",aA,"c",cA), Map.of("a","c"), """
B:{.m(x:a.A):c.A->x.fromC}
"""); }
  @Test void swapTwoPackages(){ ok(Map.of("a",aA,"c",cA), Map.of("a","c","c","a"), """
B:{
  .m1(x:a.A):a.A->x.fromC;
  .m2(y:c.A):c.A->y.fromA;
  }
"""); }
  @Test void mapIsNotTransitive(){ ok(Map.of("c",cA,"d",dA), Map.of("a","c","c","d"), """
B:{
  .m1(x:a.A):a.A->x.fromC;
  .m2(y:c.A):c.A->y.fromD;
  }
"""); }
  @Test void mapIsNotTransitiveFail(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):a.A->x.fromD}
   |    ---------------~^^^^^^^

While inspecting ".m(_)" line 1
This call to method ".fromD" cannot typecheck.
Method ".fromD" is not declared on type "c.A".

Available methods on type "c.A":
-       .fromC:c.A

Name "a.A" stands for "c.A" because of "map a as c in b".

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromD
Error 8 TypeError
""", Map.of("c",cA,"d",dA), Map.of("a","c","c","d"), """
B:{.m(x:a.A):a.A->x.fromD}
"""); }
  @Test void mapIntoTheCurrentPackage(){ ok(Map.of(), Map.of("a","b"), """
B:{.m(x:a.B):B->x.self; .self:b.B->this}
"""); }
  @Test void useThroughMapIntoTheCurrentPackage(){ ok(Map.of(), Map.of("a","b"), """
use a.B as X;
B:{.m(x:X):a.B->x.self; .self:b.B->this}
"""); }
  @Test void useOfTheCurrentPackage(){ ok(Map.of(), Map.of(), """
use b.B as X;
B:{.m(x:X):B->x.self; .self:X->this}
"""); }
  @Test void useThroughMapIntoTheCurrentPackageUndeclared(){ fail("""
In file: [###].fear

001| use a.Z as X;
   |     ^^^

While inspecting package header
Name "a.Z" stands for "b.Z" because of "map a as b in b".
"use" directive refers to undeclared name: type "Z" is not declared in package "b".
Error 7 WellFormedness
""", Map.of(), Map.of("a","b"), """
use a.Z as X;
B:{}
"""); }
  @Test void useOfTheCurrentPackageOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "X" stands for "b.B" because of "use b.B as X".
Name "B" is not declared with 1 type parameter(s) in package "b".
Name "B" is only declared with 0 type parameter(s).
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of(), Map.of(), """
use b.B as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void mapIntoTheCurrentPackageUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Name "a.Z" stands for "b.Z" because of "map a as b in b".
Type "Z" is not declared in package "b".
In scope: "B".
Error 7 WellFormedness
""", Map.of(), Map.of("a","b"), """
B:{.m(x:a.Z):B->this}
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
Name "B" is not declared with 1 type parameter(s) in package "b".
Name "B" is only declared with 0 type parameter(s).
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of(), Map.of(), """
B:{.m(x:b.B[B]):B->this}
"""); }
  @Test void mapToMissingType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
Name "a.Z" stands for "c.Z" because of "map a as c in b".
Type "Z" is not declared in package "c".
In scope: "A".
Error 7 WellFormedness
""", Map.of("a",aA,"c",cA), Map.of("a","c"), """
B:{.m(x:a.Z):B->this}
"""); }
  @Test void useThroughMap(){ ok(Map.of("a",aA,"c",cA), Map.of("a","c"), """
use a.A as A;
B:{.m(x:A):a.A->x.fromC}
"""); }
  @Test void useThroughMapInPackageMissing(){ ok(Map.of("c",cA), Map.of("a","c"), """
use a.A as A;
B:{.m(x:A):a.A->x.fromC}
"""); }
  @Test void useThroughMapToMissingType(){ fail("""
In file: [###].fear

001| use a.Z as Z;
   |     ^^^

While inspecting package header
Name "a.Z" stands for "cc.Z" because of "map a as cc in b".
"use" directive refers to undeclared name: type "Z" is not declared in package "cc".
Error 7 WellFormedness
""", Map.of("a",aA,"cc",cA), Map.of("a","cc"), """
use a.Z as Z;
B:{}
"""); }
  @Test void useThroughSwap(){ ok(Map.of("a",aA,"c",cA), Map.of("a","c","c","a"), """
use a.A as CA;
use c.A as AA;
B:{.m1(x:CA):a.A->x.fromC; .m2(y:AA):c.A->y.fromA}
"""); }
  @Test void twoVirtualPackagesMappedToTheSameRealPackage(){ ok(Map.of("c",cA), Map.of("a","c","d","c"), """
B:{.m(x:a.A):d.A->x.fromC}
"""); }
  @Test void twoUsesReachingTheSameTypeThroughMap(){ ok(Map.of("c",cA), Map.of("a","c"), """
use a.A as X;
use c.A as Y;
B:{.m(x:X):Y->x.fromC}
"""); }
  @Test void twoUsesReachingTheSameTypeThroughMapFail(){ fail("""
In file: [###].fear

003| B:{.m(x:Y):X->x.fromA}
   |    -----------~^^^^^^^

While inspecting ".m(_)" line 3
This call to method ".fromA" cannot typecheck.
Method ".fromA" is not declared on type "X".

Available methods on type "X":
-       .fromC:X

Name "Y" stands for "a.A" because of "use a.A as Y".
Name "a.A" stands for "c.A" because of "map a as c in b".
Name "X" stands for "c.A" because of "use c.A as X".

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""",Map.of("c",cA), Map.of("a","c"), """
use a.A as Y;
use c.A as X;
B:{.m(x:Y):X->x.fromA}
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
Name "a.A" stands for "c.A" because of "map a as c in b".

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromA
Error 8 TypeError
""", Map.of("a",aA,"c",cA), Map.of("a","c"), """
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
""", Map.of("c",cA), Map.of(), """
use c.A as X;
B:{.m(x:X):X->x.fromA}
"""); }
  @Test void swapTwoPackagesFail(){ fail("""
In file: [###].fear

001| B:{.m(y:c.A):c.A->y.fromC}
   |    ---------------~^^^^^^^

While inspecting ".m(_)" line 1
This call to method ".fromC" cannot typecheck.
Method ".fromC" is not declared on type "a.A".

Available methods on type "a.A":
-       .fromA:a.A

Name "c.A" stands for "a.A" because of "map c as a in b".

Compressed relevant code with inferred types: (compression indicated by `-`)
y.fromC
Error 8 TypeError
""", Map.of("a",aA,"c",cA), Map.of("a","c","c","a"), """
B:{.m(y:c.A):c.A->y.fromC}
"""); }
  @Test void useOfOtherPackageOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "X" stands for "c.A" because of "use c.A as X".
Name "A" is not declared with 1 type parameter(s) in package "c".
Name "A" is only declared with 0 type parameter(s).
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of("c",cA), Map.of(), """
use c.A as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void useThroughMapOtherArity(){ fail("""
In file: [###].fear

002| B:{.m(x:X[B]):B->this}
   |         ^^

While inspecting a type name
Name "X" stands for "a.A" because of "use a.A as X".
Name "a.A" stands for "c.A" because of "map a as c in b".
Name "A" is not declared with 1 type parameter(s) in package "c".
Name "A" is only declared with 0 type parameter(s).
Did you accidentally add or omit a type parameter?
Error 7 WellFormedness
""", Map.of("a",aA,"c",cA), Map.of("a","c"), """
use a.A as X;
B:{.m(x:X[B]):B->this}
"""); }
  @Test void mapToMissingPackage(){ fail("""
In file: [###].fear

001| B:{.m(x:a.A):B->this}
   |         ^^^^

While inspecting a type name
Name "a.A" stands for "zz.A" because of "map a as zz in b".
Package "zz" does not exist.
Visible packages: "a", "b", "base".
Error 7 WellFormedness
""", Map.of("a",aA), Map.of("a","zz"), """
B:{.m(x:a.A):B->this}
"""); }
}
