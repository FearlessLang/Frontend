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
    if (e instanceof X v && v.name().equals(x)){ acc.add(v); }
    var skipLiteral= activeOnly && e instanceof Literal;
    if (!skipLiteral){ e.children().forEach(c->collect(x, c, activeOnly, acc)); }
  }
}