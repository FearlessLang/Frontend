package typeSystem;

import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import core.B;
import core.T;
import fearlessParser.RC;
import message.TypeSystemErrors;

import static offensiveUtils.Require.*;

import static fearlessParser.RC.*;

public record ViewPointAdaptation(Kinding k){
  public sealed interface Change permits Same, Keep, Drop{
    Optional<T> view();
    Why why();
    Change map(Function<T,Change> f);
    static Change drop(Why why){ return new Drop(why); }
    static Change keep(T in, T out, Why why){ return out.equals(in) ? new Same(out) : new Keep(out, why); }
  }
  public record Same(T t) implements Change{
    public Same{ assert nonNull(t); }
    public Optional<T> view(){ return Optional.of(t); }
    public Why why(){ return (_,_,_,_,_)->""; }
    public Change map(Function<T,Change> f){ return f.apply(t); }
  }
  public record Keep(T t, Why why) implements Change{
    public Keep{ assert nonNull(t,why); }
    public Optional<T> view(){ return Optional.of(t); }
    public Change map(Function<T,Change> f){ return merge(f.apply(t)); }
    private Change merge(Change next){ return switch(next){
      case Same _->this;
      case Keep k -> new Keep(k.t(), why.then(next.why()));
      case Drop _->next;
    };}
  }
  public interface Why{
    String render(String x, T expected, Optional<T> got, T declared, List<B> bs);
    default Why then(Why next){
      return (x, expected, got, declared, bs)->{
        String a= render(x, expected, got, declared, bs);
        String b= next.render(x, expected, got, declared, bs);
        if (a.isEmpty()){ return b; }
        if (b.isEmpty()){ return a; }
        return a+"\n"+b;//TODO: later this may change in some other kind of formatting
      };
    }
  }
  public record Drop(Why why) implements Change{
    public Drop{ assert nonNull(why); }
    public Optional<T> view(){ return Optional.empty(); }
    public Change map(Function<T,Change> f){ return this; }
  }
  public Gamma of(Gamma g, List<B> delta, RC rc0, RC rc){ return g.mapFilter(t -> of(t,delta,rc0,rc)); }

  private Change of(T t, List<B> delta, RC rc0, RC rc){
    if (discard(t, delta, rc0)){ return Change.drop(TypeSystemErrors.discardWhy(t, delta, rc0,kindIsoImm(t, delta))); }
    var withImm= kindIsoImm(t, delta)
      || (rc == imm && (rc0 == mut || rc0 == read) && kindIsoImmMutRead(t, delta));
    if (withImm){ return Change.keep(t, t.withRC(imm), TypeSystemErrors.strengthenToImm(t)); }
    return adapt(t, delta, rc);
  }
  private Change adapt(T t, List<B> delta, RC rc){ // T[delta, RC]
    if (rc == read){
      if (isMutReadForm(t)){ return Change.keep(t, t.withRC(read), TypeSystemErrors.setToRead(t)); }
      if (isXReadImmXForm(t)){ return Change.keep(t, t.readImm(), TypeSystemErrors.useReadImm(t)); }
    }
    assert rc == mut;//meth RC can only be imm, mut, read and imm is filtered before
    if (kindImmMutRead(t, delta)){ return new Same(t); }
    return Change.keep(t, t.withRC(read), TypeSystemErrors.weakenedToRead(t));
  }
  private boolean discard(T t, List<B> delta, RC rc0){
    if ((rc0 == iso || rc0 == imm) && !kindIsoImm(t, delta)){ return true; }
    return !kindIsoImmMutRead(t, delta);
  } 
  private boolean kindIsoImm(T t, List<B> delta){ return k.of(delta,t,EnumSet.of(iso, imm)); }
  private boolean kindIsoImmMutRead(T t, List<B> delta){ return k.of(delta,t,EnumSet.of(iso, imm, mut, read)); }
  private boolean kindImmMutRead(T t, List<B> delta){ return k.of(delta,t,EnumSet.of(imm, mut, read)); }

  private boolean isMutReadForm(T t){
    if (t instanceof T.RCC rcc){ return rcc.rc() == mut || rcc.rc() == read; }
    if (t instanceof T.RCX rcx){ return rcx.rc() == mut || rcx.rc() == read; }
    return false;
  }
  private boolean isXReadImmXForm(T t){ return t instanceof T.X || t instanceof T.ReadImmX; }
}