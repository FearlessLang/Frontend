package inference;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import core.MName;
import core.RC;
import inference.Gamma.GammaSignature;
import utils.Range;

public final class Monotonicity{
  private Monotonicity(){}
  enum K{eT,callRc,callTarg,litMArg,litMRet}

  // Intended usage:
  // - E.t:                 kind=eT      a=0                 b=0
  // - Call.rc:             kind=callRc  a=0                 b=0
  // - Call.targs[i]:       kind=callTarg a=i                b=0
  // - Literal.ms[mi].ret:  kind=litMRet a=mi                b=0
  // - Literal.ms[mi].arg[pi]:
  //                         kind=litMArg a=mi               b=pi
  record Slot(K k, int a, int b){}

  private static boolean step(GammaSignature g, Slot slot, Object from, Object to, String what){
    var l= g.monotonicity.computeIfAbsent(slot, _->new ArrayList<>(4));
    if (l.isEmpty()){ l.add(from); }
    var last= l.getLast();
    var outOfSync= !(from instanceof IT.U) && !last.equals(from);
    if (outOfSync){
      throw new AssertionError("Monotonicity tracker out of sync for "+what
        +"\nLast="+last+"\nFrom="+from+"\nHist="+l);
    }
    if (from.equals(to)){ return true; } // after sync/init
    for (var old : l){
      if (old.equals(to)){
        throw new AssertionError("Non-monotone evolution (cycle) for "+what
          +"\nTo="+to+"\nHist="+l);
      }
    }
    l.add(to);
    return true;
  }

  public static boolean eT(E e, IT to){
    return step(e.g(), new Slot(K.eT,0,0), e.t(), to, "E.t "+e.getClass().getSimpleName());
  }

  private static boolean hasAnyKind(GammaSignature g, K k){ return g.monotonicity.keySet().stream().anyMatch(s->s.k() == k); }

  public static boolean onCallWithMore(E.Call c, Optional<RC> nextRc, List<IT> nextTargs, IT nextT){
    step(c.g(), new Slot(K.eT,0,0), c.t(), nextT, "Call.t");
    step(c.g(), new Slot(K.callRc,0,0), c.rc(), nextRc, "Call.rc");
    var oldN= c.targs().size();
    var newN= nextTargs.size();
    // Arity repair is allowed, but only before we started tracking per-index targs.
    var arityChangedWhileTracked= oldN != newN && hasAnyKind(c.g(), K.callTarg);
    if (arityChangedWhileTracked){
      throw new AssertionError("Call.targs arity changed after tracking started old="+oldN+" new="+newN
        +"\ncall="+c);
    }
    var from= oldN == newN ? c.targs() : nextTargs;
    for (int i : Range.of(nextTargs)){
      step(c.g(), new Slot(K.callTarg,i,0), from.get(i), nextTargs.get(i), "Call.targs["+i+"]");
    }
    return true;
  }

  private static boolean litStable(List<M> ms){
    return ms.stream().allMatch(m->m.sig().m().isPresent());
  }

  public static boolean onLiteralWithMs(E.Literal l, List<M> nextMs){
    // Methods may be inserted/reordered while any method has no name.
    // In that phase, we DO NOT track literal method slots at all.
    var unstable= !litStable(l.ms()) || !litStable(nextMs);
    if (unstable){
      l.g().monotonicity.keySet().removeIf(s->s.k() == K.litMArg || s.k() == K.litMRet);
      return true;
    }
    // First stable snapshot: start tracking from nextMs (not from l.ms()).
    var oldMs= hasAnyKind(l.g(),K.litMArg) || hasAnyKind(l.g(),K.litMRet) ? l.ms() : nextMs;
    var oldN= oldMs.size();
    var newN= nextMs.size();
    if (oldN != newN){
      throw new AssertionError("Literal.ms size changed after tracking started old="+oldN+" new="+newN
        +"\noldMs="+msBrief(l.ms())+"\nnewMs="+msBrief(nextMs)
        +"\nlit="+l);
    }
    // Same size, stable names: normal monotonic tracking by index.
    for (int mi : Range.of(nextMs)){
      var om= oldMs.get(mi);
      var nm= nextMs.get(mi);
      var ops= sigPs(om);
      var nps= sigPs(nm);
      if (ops.size() != nps.size()){
        var on= mName(om);
        var nn= mName(nm);
        throw new AssertionError("Literal.ms["+mi+"] arity changed old="+ops.size()+" new="+nps.size()
          +"\noldName="+on+"\nnewName="+nn+"\nnameChanged="+!on.equals(nn)
          +"\noldSig="+om.sig()+"\nnewSig="+nm.sig()
          +"\noldMs="+msBrief(l.ms())+"\nnewMs="+msBrief(nextMs)
          +"\nlit="+l);
      }
      for (int pi : Range.of(ops)){
        step(l.g(), new Slot(K.litMArg,mi,pi), ops.get(pi), nps.get(pi), "Lit.ms["+mi+"].arg["+pi+"] "+l);
      }
      step(l.g(), new Slot(K.litMRet,mi,0), sigRet(om), sigRet(nm), "Lit.ms["+mi+"].ret "+l);
    }
    return true;
  }

  private static List<IT> sigPs(M m){
    return m.sig().ts().stream().map(it->it.orElse(IT.U.Instance)).toList();
  }
  private static IT sigRet(M m){
    return m.sig().ret().orElse(IT.U.Instance);
  }
  private static String mName(M m){
    return m.sig().m().map(MName::s).orElse("<nameToInfer>");
  }
  private static List<String> msBrief(List<M> ms){
    return ms.stream().map(m->mName(m)+"/"+sigPs(m).size()).toList();
  }
}