package typeSystem;

import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import core.B;
import core.T;
import fearlessParser.RC;

import static fearlessParser.RC.*;

public record ViewPointAdaptation(Kinding k){
  public Gamma of(Gamma g, List<B> delta, RC rc0, RC rc){ return g.mapFilter(t -> of(t,delta,rc0,rc)); }
  
  private Optional<T> of(T t, List<B> delta, RC rc0, RC rc){
    if (discard(t, delta, rc0)){ return Optional.empty(); }
    var withImm= kindIsoImm(t, delta) 
      || (rc == imm && (rc0 == mut || rc0 == read) && kindIsoImmMutRead(t, delta));
    if (withImm){ return Optional.of(t.withRC(imm)); }
    return Optional.of(adapt(t, delta, rc));
  }  
  private T adapt(T t, List<B> delta, RC rc){ // T[delta, RC]
    if (rc == read){
      if (isMutReadForm(t)){ return t.withRC(read); }
      if (isXReadImmXForm(t)){ return t.readImm(); }
    }
    assert rc == mut;//meth RC can only be imm, mut, read and imm is filtered before
    if (kindImmMutRead(t, delta)){ return t; }
    return t.withRC(read);
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