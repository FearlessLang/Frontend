package typeSystem;

import java.util.ArrayList;
import java.util.List;

import core.E;
import core.E.*;
import core.M;
import message.TypeSystemErrors;

class Affine{
  static void usedOnce(TypeSystemErrors err, Literal l,M m, String x, E e){
    List<X> active= new ArrayList<>();
    collect(x, e, true, active);
    if (active.isEmpty()){ return; }
    if (active.size() > 1){ throw err.notAffineIso(l,m, x,true, active); }
    List<X> total= new ArrayList<>();
    collect(x, e, false, total);
    if (total.size() > 1){ throw err.notAffineIso(l,m, x,false, total); }
  }
  private static void collect(String x, E e, boolean activeOnly, List<X> acc){
    switch (e){
      case X v -> { if (v.name().equals(x)){ acc.add(v); } }
      case Call c -> collectCall(x, c, activeOnly, acc);
      case Literal l -> collectLiteral(x, l, activeOnly, acc);
      case Type _ -> {}
    }
  }
  private static void collectCall(String x, Call c, boolean activeOnly, List<X> acc){
    collect(x, c.e(), activeOnly, acc);
    for (var arg : c.es()){ collect(x, arg, activeOnly, acc); }
  }
  private static void collectLiteral(String x, Literal l, boolean activeOnly, List<X> acc){
    if (activeOnly){ return; }
    for (M m : l.ms()){ m.e().ifPresent(e -> collect(x, e, false, acc)); }
  }
}