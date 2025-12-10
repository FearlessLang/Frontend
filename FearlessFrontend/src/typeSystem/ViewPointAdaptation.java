package typeSystem;

import java.util.EnumSet;
import java.util.List;
import core.*;
import core.E.*;
import fearlessParser.RC;
import message.TypeSystemErrors;
import typeSystem.Change.*;
import static fearlessParser.RC.*;

public record ViewPointAdaptation(Kinding k){
  TypeSystemErrors err(){ return k.err(); }
  public Gamma of(Gamma g, List<B> delta, Literal l, M m){ return g.mapFilter(t -> of(t,delta,l,m)); }
  private Change of(T t, List<B> delta, Literal l, M m){    //Literal l, M m, T atDrop
    RC rc0= l.rc();
    RC rc=  m.sig().rc();
    if (discard(t, delta, rc0)){ return Change.drop(err().discardWhy(l,m,t)); }//TODO: it was , delta, rc0,kindIsoImm(t, delta) and we may need it again for good errors
    var withImm= kindIsoImm(t, delta)
      || (rc == imm && (rc0 == mut || rc0 == read) && kindIsoImmMutRead(t, delta));
    if (withImm){ return Change.keep(t, t.withRC(imm), err().strengthenToImm(t)); }
    return adapt(t, delta, rc);
  }
  private Change adapt(T t, List<B> delta, RC rc){ // T[delta, RC]
    if (rc == read){
      if (isMutReadForm(t)){ return Change.keep(t, t.withRC(read), err().setToRead(t)); }
      if (isXReadImmXForm(t)){ return Change.keep(t, t.readImm(), err().useReadImm(t)); }
    }
    assert rc == mut;//meth RC can only be imm, mut, read and imm is filtered before
    if (kindImmMutRead(t, delta)){ return new Same(t); }
    return Change.keep(t, t.withRC(read), err().weakenedToRead(t));
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