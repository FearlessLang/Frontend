package typeSystem;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

import core.B;
import core.RC;
import core.T;
import core.TName;
import core.TSpan;
import utils.Pos;

public class EqModXRCTest{
  static final TSpan span= TSpan.fromPos(Pos.unknown);
  static final T.X x= new T.X("X",span);
  static final TName foo= new TName("Foo",0,Pos.unknown);
  static final TName box= new TName("Box",1,Pos.unknown);
  static final List<T> spellings= Stream.concat(
    Stream.<T>of(x,new T.ReadImmX(x)),
    Arrays.stream(RC.values()).<T>map(rc->new T.RCX(rc,x))).toList();
  static final List<T> types= Stream.concat(spellings.stream(),
    spellings.stream().<T>map(s->new T.RCC(RC.imm,new T.C(box,List.of(s)),span))).toList();
  static final List<EnumSet<RC>> bounds= IntStream.range(1,1<<RC.values().length).mapToObj(EqModXRCTest::bound).toList();
  static EnumSet<RC> bound(int mask){
    var res= EnumSet.noneOf(RC.class);
    for (var rc : RC.values()){ if ((mask & 1<<rc.ordinal()) != 0){ res.add(rc); } }
    return res;
  }
  static boolean eq(EnumSet<RC> rcs,T a,T b){ return TypeSystem.eqModXRC(List.of(new B("X",rcs)),a,b); }
  static T inst(T t,RC rc){ return switch (t){
    case T.X _ -> new T.RCC(rc,new T.C(foo,List.of()),span);
    case T.RCX(var rcx, _) -> new T.RCC(rcx,new T.C(foo,List.of()),span);
    case T.ReadImmX _ -> new T.RCC(rc.readImm(),new T.C(foo,List.of()),span);
    case T.RCC(var rcc, var c, _) -> new T.RCC(rcc,c.withTs(c.ts().stream().map(ti->inst(ti,rc)).toList()),span);
  };}
  static boolean sameInstances(EnumSet<RC> rcs,T a,T b){ return rcs.stream().allMatch(rc->inst(a,rc).equals(inst(b,rc))); }
  static List<String> violations(Check check){
    var res= new ArrayList<String>();
    for (var rcs : bounds){ for (var a : types){ for (var b : types){
      if (!check.holds(rcs,a,b)){ res.add(rcs+" "+a+" "+b); }
    }}}
    return res;
  }
  interface Check{ boolean holds(EnumSet<RC> rcs,T a,T b); }
  @Test void equalSpellingsDenoteTheSameTypeForEveryCapabilityOfTheBound(){
    assertEquals(List.of(),violations((rcs,a,b)->!eq(rcs,a,b) || sameInstances(rcs,a,b)));
  }
  @Test void equalSpellingsStayEqualUnderEverySmallerBound(){
    assertEquals(List.of(),violations((rcs,a,b)->!eq(rcs,a,b)
      || bounds.stream().filter(rcs::containsAll).allMatch(smaller->eq(smaller,a,b))));
  }
  @Test void underASingleCapabilityBoundSpellingsDenotingTheSameTypeAreEqual(){
    assertEquals(List.of(),violations((rcs,a,b)->rcs.size() != 1 || eq(rcs,a,b) == sameInstances(rcs,a,b)));
  }
  @Test void underABoundOfSeveralCapabilitiesSpellingsAreComparedAsWritten(){
    assertEquals(List.of(),violations((rcs,a,b)->rcs.size() == 1 || eq(rcs,a,b) == a.equals(b)));
  }
}
