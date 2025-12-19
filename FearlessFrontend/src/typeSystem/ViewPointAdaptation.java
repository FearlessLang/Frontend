package typeSystem;

import java.util.EnumSet;
import java.util.List;

import core.*;
import core.E.*;
import fearlessParser.RC;
import typeSystem.Change.*;
import static fearlessParser.RC.*;

public record ViewPointAdaptation(Kinding k){
  public Gamma of(Gamma g,Literal l, M m){ return g.map(curr -> of(curr,l,m)); }
  private Change of(Change current, Literal l, M m){    //Literal l, M m, T atDrop
    if(!( current instanceof Change.WithT w)){ return current; }
    T t= w.currentT();
    RC rc0= l.rc();
    RC rc=  m.sig().rc();
    Change oc= discard(w, l);
    if(oc instanceof Change.NoT){ return oc; }
    boolean withImm= kindIsoImm(t, l.bs())
      || (rc == imm && (rc0 == mut || rc0 == read) && kindIsoImmMutRead(t, l.bs()));
    if (withImm){ return Change.keepStrengthenToImm(l,m,w); }
    return adapt(w, l, m);
  }
  private Change adapt(WithT w, Literal l, M m){ // T[delta, RC]
    RC rc= m.sig().rc();
    T t=w.currentT();
    if (rc == read){
      if (isMutReadForm(t)){ return Change.keepSetToRead(l,m,w); }
      if (isXReadImmXForm(t)){ return Change.keepSetToReadImm(l,m,w); }
    }
    assert rc == mut;//meth RC can only be imm, mut, read and imm is filtered before
    if (kindImmMutRead(t, l.bs())){ return w; }
    return Change.keepSetToRead(l,m,w);
  }
  private Change discard(Change.WithT w, Literal l){
    var t= w.currentT();
    if (!kindIsoImmMutRead(t, l.bs())){ return Change.dropReadHMutH(l,t); }
    if ((l.rc() == iso || l.rc() == imm) && !kindIsoImm(t, l.bs())){ return Change.dropMutInImm(l,t); }
    return w;
    
    //Used to be as below, but the above gives better errors (prioritizes dropReadHMutH) 
    //if ((l.rc() == iso || l.rc() == imm) && !kindIsoImm(t, l.bs())){ return Optional.of(Change.dropMutInImm(l,t)); }
    //if (kindIsoImmMutRead(t, l.bs())){ return Optional.empty(); };
    //return Optional.of(Change.dropReadHMutH(l,t));
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