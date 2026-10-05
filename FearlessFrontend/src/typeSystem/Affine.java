package typeSystem;

import java.util.ArrayList;

import core.E;
import core.E.*;
import core.M;
import message.TypeSystemErrors;

final class Affine{
  private Affine(){}
  static void usedOnce(TypeSystemErrors err, Literal l,M m, String x){
    var active= new ArrayList<X>();
    collect(x, m.e().get(), true, active);
    //Intentionally allowing multiple captures as imm: equivalent to cast to imm and then capture multiple times
    if (active.isEmpty()){ return; }
    if (active.size() > 1){ throw err.notAffineIso(l,m, x,true, active); }
    var total= new ArrayList<X>();
    collect(x, m.e().get(), false, total);
    if (total.size() > 1){ throw err.notAffineIso(l,m, x,false, total); }
  }
  private static void collect(String x, E e, boolean activeOnly, ArrayList<X> acc){
    switch (e){
      case X v -> { if (v.name().equals(x)){ acc.add(v); } }
      case Call c -> { collect(x, c.e(), activeOnly, acc); c.es().forEach(arg->collect(x, arg, activeOnly, acc)); }
      case Literal l -> { if (!activeOnly){ l.ms().forEach(m->m.e().ifPresent(e1->collect(x, e1, false, acc))); } }
      case Type _ -> {}
    }
  }
}