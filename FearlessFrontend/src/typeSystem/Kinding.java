package typeSystem;
import static core.RC.*;
import static offensiveUtils.Require.*;
import java.util.EnumSet;
import java.util.List;
import java.util.function.Function;

import core.*;
import core.E.*;
import message.TypeSystemErrors;
import utils.Range;
import utils.Streams;

public record Kinding(TypeSystemErrors tsE){
  public void checkC(E toErr, List<B> bs, T.C c){
    var d= decs().apply(c.name());
    var params= d.bs();
    var args= c.ts();
    assert eq(params.size(), args.size(), "Arity mismatch for " + c.name());
    for (int i : Range.of(params)){ check(toErr, c, i, bs, args.get(i), params.get(i).rcs()); }
  }
  public void check(E toErr, List<B> bs, T t){
    if (t instanceof T.RCC rcc){ check(toErr,rcc,-1,bs,rcc,EnumSet.allOf(RC.class)); }
  }
  public Function<TName,Literal> decs(){ return tsE.decs(); }
  public void check(E toErr, KindingTarget target, int index, List<B> bs, T t, EnumSet<RC> allowed){
    if (t instanceof T.RCC rcc){
      if (!allowed.contains(rcc.rc())){ throw tsE.typeNotWellKinded(toErr,target,index,allowed); }
      checkC(toErr,bs,rcc.c());
      return;
    }
    if (!of(bs,t,allowed)){ throw tsE.typeNotWellKinded(toErr,target,index,allowed); }
  }
  public boolean of(List<B> bs, T t, EnumSet<RC> allowed){
    if (!allowed.containsAll(intrinsicRCs(bs, t))){ return false; }
    if (!(t instanceof T.RCC rcc)){ return true; }
    var params= decs().apply(rcc.c().name()).bs();
    return Streams.zip(rcc.c().ts(), params).allMatch((ti,p)->of(bs, ti, p.rcs()));
  }
  static EnumSet<RC> intrinsicRCs(List<B> bs, T t){ return switch (t){
    case T.RCC(var rc, _,_) -> EnumSet.of(rc);
    case T.RCX(var rc, _) -> EnumSet.of(rc);
    case T.X(var x,_) -> get(bs, x).rcs();
    case T.ReadImmX(var x) -> readImmRCs(intrinsicRCs(bs, x));
  };}
  private static EnumSet<RC> readImmRCs(EnumSet<RC> rcs){
    if (EnumSet.of(iso, imm).containsAll(rcs)){ return EnumSet.of(imm); }
    if (EnumSet.of(mut, mutH, read, readH).containsAll(rcs)){ return EnumSet.of(read); }
    return EnumSet.of(read, imm);
  }
}