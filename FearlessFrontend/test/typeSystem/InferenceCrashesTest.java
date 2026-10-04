package typeSystem;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Test;

public class InferenceCrashesTest extends testUtils.FearlessTestBase{
  static void ok(String input){ typeOk(List.of(input)); }
  static void failExt(String expected, String input){ typeFailRaw(expected, List.of(input)); }

@Test void manyConsecutiveLetsInOneMethod(){
  var lets= IntStream.rangeClosed(1,128).mapToObj(i->".let x"+i+"= {5} ").collect(Collectors.joining());
  ok("use base.Nat as Nat; User:{ .u: Nat -> base.Block#"+lets+".return {x1} }");}
@Test void writtenResultTypeMentioningMethodTypeParameterOnlyThere(){
  failExt("[###]Parameter \"this\" has type \"T1\" instead of a subtype of \"Z[Y]\".[###]Error 8 TypeError",
    "Z[X]:{ } T1:{ .m[Y]: T1 -> { .k: Z[Y] -> this } }");}
@Test void literalInBodyOfMethodImplementingReadAndImmOverloads(){
  ok("A:{ .k: A -> this } T0:{ .m: A; } T1:T0{ read .m: A -> A } U:{ .u: T1 -> T1{ .m: A -> A{ .k: A -> A } } }");}
@Test void receiverLiteralWithUndeterminedTypeArgumentIsRejectedForMissingMethod(){
  failExt("[###]","T0[X0,X1]:{ .m2(x: X0): base.Void; .m0: T0[X0, base.Void] -> {}.m0 }");}
@Test void receiverLiteralWithUndeterminedTypeArgumentCapturingThis(){
  failExt("[###]","T0[X]:{ .m: T0[base.Void] -> {this}.m }");}
@Test void expansiveSupertypeDoesNotMakeInferenceRecurseForever(){
  failExt("[###]","T0[X]:{ } T1:T0[T0[T1]]{ .m(a: T0[T1]): T1 -> this.m(this) }");}
@Test void reAbstractedMethodBesideAnUnrelatedImplementation(){
  try{ ok("R:{ } A:{ .m: R -> R } B:{ .m: R -> R } C:B{ .m: R; } D:A,C{ }"); }
  catch(core.FearlessException _){}}
}
