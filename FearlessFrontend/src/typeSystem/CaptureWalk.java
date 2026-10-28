package typeSystem;

import java.util.List;
import java.util.function.Predicate;

import core.B;
import core.E;
import core.RC;
import core.T;

record CaptureWalk(List<B> bs, Gamma g, Predicate<RC> freeRC){
  //NOTE: we could be more permissive skipping m.sig().rc() == RC.imm
  //but is not that obvious. iso {imm .foo->captMut} fails but
  //mut {imm .foo->captMut} may pass. The same reason we can skip imm methods is reason to
  //not promote mut->iso?
  boolean isFree(E e){ return e instanceof E.X x ? isFree(x) : e.children().allMatch(this::isFree); }
  private boolean isFree(E.X x){
    var cur= g._bind(x.name());
    if (cur == null){ return true; }
    if (!(cur.current() instanceof Change.WithT w)){ return true; }
    var t= w.currentT() instanceof T.ReadImmX(var y) ? y : w.currentT();
    return Kinding.intrinsicRCs(bs, t).stream().allMatch(freeRC);
  }
}