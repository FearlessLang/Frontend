package typeSystem;

import static core.RC.*;

import java.util.EnumSet;
import java.util.List;

import core.*;
import core.E.*;
import typeSystem.Change.*;

public record ViewPointAdaptation(Kinding k){
  public Gamma discard(Gamma g, Literal l){ return g.map(curr -> discard(curr, l)); }
  public Gamma of(Gamma g, Literal l, M m){ return g.map(curr -> of(curr, l, m)); }
  private Change of(Change current, Literal l, M m){    //Literal l, M m, T atDrop
    if (!(current instanceof Change.WithT w)){ return current; }
    var withImm= m.sig().rc() == imm || kindIsoImm(w.currentT(), l.bs());
    if (withImm){ return Change.keepStrengthenToImm(l, m, w); }
    return adapt(w, l, m);
  }
  private Change adapt(WithT w, Literal l, M m){ // T[delta, RC]
    var toReadImm= m.sig().rc() == read || !k.of(l.bs(), w.currentT(), EnumSet.of(imm, mut, read));
    return toReadImm ? Change.keepSetToReadImm(l, m, w) : w;
  }
  private Change discard(Change current, Literal l){
    if (!(current instanceof Change.WithT w)){ return current; }
    var t= w.currentT();
    var notKinded= !k.of(l.bs(), t, EnumSet.allOf(RC.class));
    if (notKinded){ return new Change.DropNotKinded(l, t); }
    var mayBeHygienic= !k.of(l.bs(), t, EnumSet.of(iso, imm, mut, read));
    if (mayBeHygienic){ return new Change.DropReadHMutH(l, t); }
    var mutInImm= l.rc().isIsoOrImm() && !kindIsoImm(t, l.bs());
    if (mutInImm){ return new Change.DropMutInImm(l, t); }
    return w;
  }
  private boolean kindIsoImm(T t, List<B> delta){ return k.of(delta, t, EnumSet.of(iso, imm)); }
}