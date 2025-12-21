package typeSystem;

import static core.RC.*;

import java.util.*;
import java.util.stream.IntStream;

import core.B;
import core.RC;
import core.T;
import typeSystem.TypeSystem.MType;
import utils.OneOr;

class MultiMeth{
  private enum F{
    lub{ @Override RC of(EnumSet<RC> rcs){ return RCLubGlb.lub(rcs); } },
    glb{ @Override RC of(EnumSet<RC> rcs){ return RCLubGlb.glb(rcs); } };
    abstract RC of(EnumSet<RC> rcs);
  }
  private enum Mode{
    useRead{ @Override RC of(RC rc){ return switch(rc){
      case mut -> iso;
      case read -> readH;
      default -> rc;
    };}},
    flexy{ @Override RC of(RC rc){ return switch(rc){
      case mut -> iso;
      case read -> imm;
      default -> rc;
    };}},
    hyg{ @Override RC of(RC rc){ return switch(rc){
      case mut -> mutH;
      case read -> readH;
      default -> rc;
    };}},
    strong{ @Override RC of(RC rc){ return switch(rc){
      case mut, mutH -> iso;
      case read, readH -> imm;
      default -> rc;
    };}};
    abstract RC of(RC rc);
  }
  public static List<MType> of(List<B> d, MType mType){
    var out= new LinkedHashMap<Key,MType>();
    add(out,mType);
    add(out,apply("Strengthen result",d,mType,Mode.flexy,F.glb,Mode.flexy,F.lub));
    add(out,apply("Strengthen hygienic result",d,mType,Mode.strong,F.glb,Mode.strong,F.lub));
    add(out,apply("Allow readH arguments",d,mType,Mode.useRead,F.glb,Mode.hyg,F.lub));
    oneMutHToMut(out,d,mType);
    return out.values().stream().toList();
  }
  private static void oneMutHToMut(LinkedHashMap<Key,MType> out, List<B> d, MType m){
    var tsi= IntStream.range(0, m.ts().size())
      .mapToObj(j->modeF(d,m.ts().get(j), Mode.flexy, F.glb)).toList();
    var t= modeF(d,m.t(), Mode.hyg, F.lub);
    add(out,new MType("Allow mutH receiver", Mode.hyg.of(m.rc()), tsi, t));
    for(int i= 0; i < m.ts().size(); i++){ iMutHToMut(out,d,m,i); } 
  }
  private static void iMutHToMut(LinkedHashMap<Key,MType> out, List<B> d, MType m, int i){
    var tsi= IntStream.range(0, m.ts().size())
      .mapToObj(j->modeF(d,m.ts().get(j), j == i ? Mode.hyg : Mode.flexy, F.glb)).toList();
    var t= modeF(d,m.t(), Mode.hyg, F.lub);
    add(out,new MType("Allow mutH argument "+(i+1), Mode.flexy.of(m.rc()), tsi, t));
  }
  private static MType apply(String promotion, List<B> d, MType m, Mode modeP, F fP, Mode modeR, F fR){
    List<T> ts= m.ts().stream().map(ti->modeF(d,ti,modeP,fP)).toList();
    var t= modeF(d,m.t(),modeR,fR);
    return new MType(promotion, modeP.of(m.rc()), ts, t);
  }
  private static T modeF(List<B> d, T t, Mode mode, F f){
    return switch(t){
      case T.RCC rcc -> rcc.withRC(mode.of(rcc.rc()));
      case T.RCX rcx -> rcx.withRC(mode.of(rcx.rc()));
      case T.X x -> modeVar(d,x,mode,f,t);
      case T.ReadImmX(var x) -> modeReadImmVar(d,x,mode,f,(T.ReadImmX)t);
      //Note: T.C is not a type (only a part of a type); formalism correctly does not recurse into c.ts()
    };
  }
  private static T modeVar(List<B> d, T.X x, Mode mode, F f, T original){
    var rcs= get(d,x.name());
    if (noChange(mode,rcs)){ return original; }
    var mapped= EnumSet.noneOf(RC.class);
    rcs.forEach(rc -> mapped.add(mode.of(rc)));
    return new T.RCX(f.of(mapped),x);
  }
  private static T modeReadImmVar(List<B> d, T.X x, Mode mode, F f, T.ReadImmX original){
    var rcs= get(d,x.name());
    if (noChangeRI(mode,rcs)){ return original; }
    var mapped= EnumSet.noneOf(RC.class);
    rcs.forEach(rc -> mapped.add(mode.of(rc).readImm()));
    return new T.RCX(f.of(mapped),x);
  }

  private static boolean noChange(Mode mode, EnumSet<RC> rcs){
    return rcs.stream().allMatch(rc -> mode.of(rc) == rc);
  }
  private static boolean noChangeRI(Mode mode, EnumSet<RC> rcs){
    return rcs.stream().allMatch(rc -> mode.of(rc).readImm() == rc);
  }
  private static EnumSet<RC> get(List<B> bs, String x){
    B b= OneOr.of("bad delta",bs.stream().filter(bi->bi.x().equals(x)));
    assert !b.rcs().isEmpty() :"Missing/empty Delta for "+x;
    return b.rcs();
  }
  private record Key(RC rc, List<T> ts, T t){}
  private static void add(LinkedHashMap<Key,MType> out, MType m){
    var k= new Key(m.rc(),m.ts(),m.t());
    out.merge(k,m,(a,b)->a.withPromotion(a.promotion()+", "+b.promotion()));
  }
}