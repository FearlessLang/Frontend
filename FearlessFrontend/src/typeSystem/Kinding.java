package typeSystem;
import static fearlessParser.RC.*;
import static offensiveUtils.Require.*;
import java.util.EnumSet;
import java.util.List;
import java.util.function.Function;

import core.B;
import core.E.Literal;
import core.T;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import message.TypeSystemErrors;
import utils.Bug;

public record Kinding(Function<TName,Literal> decs){
  public void check(List<B> bs, T t){ check(bs,t,EnumSet.allOf(RC.class)); }
  public void check(List<B> bs, T t,EnumSet<RC> allowed){
    if (of(bs, t, allowed)){ return; }
    throw TypeSystemErrors.notKinded(t);
  }
  public boolean of(List<B> bs, T t, EnumSet<RC> allowed){ return switch(t){
    case T.RCC rcc -> ofRCC(bs, rcc, allowed);
    case T.RCX rcx -> ofRCX(bs, rcx, allowed);
    case T.X x -> ofX(bs, x, allowed);
    case T.ReadImmX rix -> ofReadImmX(bs, rix, allowed);
  };}
  private boolean ofRCC(List<B> bs, T.RCC rcc, EnumSet<RC> allowed){
    if (!allowed.contains(rcc.rc())){ return false; }
    var d= decs.apply(rcc.c().name());
    var params = d.bs();
    var args= rcc.c().ts();
    assert eq(params.size(), args.size(), "Arity mismatch for " + rcc.c().name());
    for (int i= 0; i < params.size(); i++){
      if (!of(bs, args.get(i), EnumSet.copyOf(params.get(i).rcs()))){ return false; }
    }
    return true;
  }
  private boolean ofRCX(List<B> bs, T.RCX rcx, EnumSet<RC> allowed){
    return allowed.contains(rcx.rc());
  }
  private boolean ofX(List<B> bs, T.X x, EnumSet<RC> allowed){
    return allowed.containsAll(get(bs, x.name()).rcs());
  }
  private boolean ofReadImmX(List<B> bs, T.ReadImmX rix, EnumSet<RC> allowed){
    var rcs= get(bs, rix.x().name()).rcs();
    if (EnumSet.of(iso, imm).containsAll(rcs)){ return allowed.contains(imm); }
    if (EnumSet.of(mut, mutH, read, readH).containsAll(rcs)){ return allowed.contains(read); }
    return allowed.contains(imm) && allowed.contains(read);
  }
  private B get(List<B> bs, String name){
    for (var b : bs){ if (b.x().equals(name)){ return b; } }
    throw Bug.unreachable();
  }
}