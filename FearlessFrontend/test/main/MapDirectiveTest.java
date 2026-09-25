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
    for (var e:pkgs.entrySet()){
      var o= oraclePkg(List.of(e.getValue()));
      var lits= compileAll(e.getKey(), o, otherFrom(DbgBlock.all()));
      res= res.mergeWith(AllLs.of(lits), -1);
    }
    return res;
  }
  static void ok(Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    okOrPrint(o, ()->new FrontendLogicMain().of("b", map, o.allFiles(), o, other));
  }
  static void fail(String expected, Map<String,String> pkgs, Map<String,String> map, String bSrc){
    var o= oraclePkg(List.of(bSrc));
    var other= others(pkgs);
    var fe= assertThrows(FearlessException.class, ()->new FrontendLogicMain().of("b", map, o.allFiles(), o, other));
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

Compressed relevant code with inferred types: (compression indicated by `-`)
x.fromD
Error 8 TypeError
""", Map.of("c",cA,"d",dA), Map.of("a","c","c","d"), """
B:{.m(x:a.A):a.A->x.fromD}
"""); }
  @Test void mapIntoTheCurrentPackage(){ ok(Map.of(), Map.of("a","b"), """
B:{.m(x:a.B):B->x.self; .self:b.B->this}
"""); }
  @Test void mapIntoTheCurrentPackageUndeclared(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
[###]
Error 7 WellFormedness
""", Map.of(), Map.of("a","b"), """
B:{.m(x:a.Z):B->this}
"""); }
  @Test void mapToMissingType(){ fail("""
In file: [###].fear

001| B:{.m(x:a.Z):B->this}
   |         ^^^^

While inspecting a type name
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
}
