package typeSystem;

import static core.RC.*;

import java.util.*;
import java.util.function.Function;
import java.util.function.UnaryOperator;
import java.util.stream.IntStream;

import core.B;
import core.RC;
import core.T;
import typeSystem.TypeSystem.MType;
import utils.Range;

final class MultiMeth{
  private MultiMeth(){}
  private enum Mode{
    useRead(iso,readH,mutH,readH), flexy(iso,imm,mutH,readH), hyg(mutH,readH,mutH,readH), strong(iso,imm,iso,imm);
    final RC m, r, mh, rh;
    Mode(RC m, RC r, RC mh, RC rh){ this.m= m; this.r= r; this.mh= mh; this.rh= rh; }
    RC of(RC rc){ return switch (rc){ case mut -> m; case read -> r; case mutH -> mh; case readH -> rh; default -> rc; }; }
  }
  public static List<MType> of(List<B> d, MType mType, boolean hyg){
    var out= new LinkedHashMap<Key,MType>();
    add(out,mType);
    add(out,apply("Strengthen result",d,mType,Mode.flexy,Mode.flexy));
    if (!hyg){ return List.copyOf(out.values()); }
    add(out,apply("Strengthen hygienic result",d,mType,Mode.strong,Mode.strong));
    add(out,apply("Allow readH arguments",d,mType,Mode.useRead,Mode.hyg));
    oneMutHToMut(out,d,mType);
    return List.copyOf(out.values());
  }
  private static void oneMutHToMut(LinkedHashMap<Key,MType> out, List<B> d, MType m){
    var tsi= m.ts().stream().map(ti->modeF(d,ti, Mode.flexy, RCLubGlb::glb)).toList();
    add(out,new MType("Allow mutH receiver", Mode.hyg.of(m.rc()), tsi, modeF(d,m.t(), Mode.hyg, RCLubGlb::lub)));
    for (int i : Range.of(m.ts())){ iMutHToMut(out,d,m,i); }
  }
  private static void iMutHToMut(LinkedHashMap<Key,MType> out, List<B> d, MType m, int i){
    var tsi= IntStream.range(0, m.ts().size())
      .mapToObj(j->modeF(d,m.ts().get(j), j == i ? Mode.hyg : Mode.flexy, RCLubGlb::glb)).toList();
    var t= modeF(d,m.t(), Mode.hyg, RCLubGlb::lub);
    add(out,new MType("Allow mutH argument "+(i+1), Mode.flexy.of(m.rc()), tsi, t));
  }
  private static MType apply(String promotion, List<B> d, MType m, Mode modeP, Mode modeR){
    List<T> ts= m.ts().stream().map(ti->modeF(d,ti,modeP,RCLubGlb::glb)).toList();
    var t= modeF(d,m.t(),modeR,RCLubGlb::lub);
    return new MType(promotion, modeP.of(m.rc()), ts, t);
  }
  private static T modeF(List<B> d, T t, Mode mode, Function<EnumSet<RC>,RC> f){
    return switch (t){
      case T.RCC rcc -> rcc.withRC(mode.of(rcc.rc()));
      case T.RCX rcx -> rcx.withRC(mode.of(rcx.rc()));
      case T.X x -> modeVar(d,x,mode::of,f,t);
      case T.ReadImmX(var x) -> modeVar(d,x,rc->mode.of(rc).readImm(),f,t);
      //Note: T.C is not a type (only a part of a type); formalism correctly does not recurse into c.ts()
    };
  }
  private static T modeVar(List<B> d, T.X x, UnaryOperator<RC> m, Function<EnumSet<RC>,RC> f, T original){
    var rcs= RC.get(d,x.name()).rcs();
    var unchanged= rcs.stream().allMatch(rc->m.apply(rc) == rc);
    if (unchanged){ return original; }
    var mapped= EnumSet.noneOf(RC.class);
    rcs.forEach(rc->mapped.add(m.apply(rc)));
    return new T.RCX(f.apply(mapped),x);
  }
  private record Key(RC rc, List<T> ts, T t){}
  private static void add(LinkedHashMap<Key,MType> out, MType m){
    var k= new Key(m.rc(),m.ts(),m.t());
    out.merge(k,m,(a,b)->a.withPromotion(a.promotion()+", "+b.promotion()));
  }
}