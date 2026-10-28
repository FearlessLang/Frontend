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
  private enum Mode{
    useRead(iso, readH, mutH, readH), flexy(iso, imm, mutH, readH), hyg(mutH, readH, mutH, readH), strong(iso, imm, iso, imm);
    final RC m, r, mh, rh;
    Mode(RC m, RC r, RC mh, RC rh){ this.m= m; this.r= r; this.mh= mh; this.rh= rh; }
    RC of(RC rc){ return switch (rc){ case mut -> m; case read -> r; case mutH -> mh; case readH -> rh; default -> rc; }; }
  }
  public static List<MType> of(List<B> d, MType mType, boolean hyg){
    var out= new LinkedHashMap<Key,MType>();
    add(out, mType);
    add(out, apply("Strengthen result", d, mType, Mode.flexy, Mode.flexy, -1, Mode.flexy));
    if (!hyg){ return List.copyOf(out.values()); }
    add(out, apply("Strengthen hygienic result", d, mType, Mode.strong, Mode.strong, -1, Mode.strong));
    add(out, apply("Allow readH arguments", d, mType, Mode.useRead, Mode.useRead, -1, Mode.hyg));
    add(out, apply("Allow mutH receiver", d, mType, Mode.hyg, Mode.flexy, -1, Mode.hyg));
    for (int i : Range.of(mType.ts())){ add(out, apply("Allow mutH argument "+(i+1), d, mType, Mode.flexy, Mode.flexy, i, Mode.hyg)); }
    return List.copyOf(out.values());
  }
  private static MType apply(String promotion, List<B> d, MType m, Mode modeRecv, Mode modeP, int hygAt, Mode modeR){
    var ts= IntStream.range(0, m.ts().size()).mapToObj(j -> modeF(d, m.ts().get(j), j == hygAt ? Mode.hyg : modeP, RCLubGlb::glb)).toList();
    return new MType(promotion, modeRecv.of(m.rc()), ts, modeF(d, m.t(), modeR, RCLubGlb::lub));
  }
  private static T modeF(List<B> d, T t, Mode mode, Function<EnumSet<RC>,RC> f){
    return switch (t){
      case T.RCC rcc -> rcc.withRC(mode.of(rcc.rc()));
      case T.RCX rcx -> rcx.withRC(mode.of(rcx.rc()));
      case T.X x -> modeVar(d, x, rc -> rc, mode, f, t);
      case T.ReadImmX(var x) -> modeVar(d, x, RC::readImm, mode, f, t);
      //Note: T.C is not a type (only a part of a type); formalism correctly does not recurse into c.ts()
    };
  }
  private static T modeVar(List<B> d, T.X x, UnaryOperator<RC> inst, Mode mode, Function<EnumSet<RC>,RC> f, T original){
    var rcs= EnumSet.noneOf(RC.class);
    B.get(d, x.name()).rcs().forEach(rc -> rcs.add(inst.apply(rc)));
    var unchanged= rcs.stream().allMatch(rc -> mode.of(rc) == rc);
    if (unchanged){ return original; }
    var mapped= EnumSet.noneOf(RC.class);
    rcs.forEach(rc -> mapped.add(mode.of(rc)));
    return new T.RCX(f.apply(mapped), x);
  }
  private record Key(RC rc, List<T> ts, T t){}
  private static void add(LinkedHashMap<Key,MType> out, MType m){
    var k= new Key(m.rc(), m.ts(), m.t());
    out.merge(k, m, (a,b) -> a.withPromotion(a.promotion()+", "+b.promotion()));
  }
}