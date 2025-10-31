package fullWellFormedness;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import static java.util.Optional.of;
import static java.util.Optional.empty;
import inferenceGrammar.E;
import inferenceGrammar.Gamma;
import inferenceGrammar.IT;
import inferenceGrammarB.Declaration;

record Data(Gamma g, E e){}
public record InjectionSteps(ArrayList<Declaration> ds){
  public static List<Declaration> steps(List<Declaration> res, int steps){
    var s= new InjectionSteps(new ArrayList<>(res));
    for (int i= 0; i < s.ds.size(); i += 1){//ds.size will grow during iteration
      Declaration di= s.ds.get(i);
      for (var m:di.ms()){
        if (m.impl().isEmpty()){ continue; }
        E ei= meet(m.impl().get().e(),TypeRename.tToIT(m.sig().ret())).get();
        Gamma g= Gamma.of(m.impl().get().xs(),m.sig().ts());
        Data d=new Data(g,ei);
        while (steps-->0 && end(d=s.next(d))){}
      }
    }    
    return s.ds;
  }
  static Optional<E> meet(E e, IT t){ return meet(e.t(),t).map(ti->e.withT(ti)); }
  static Optional<IT> meet(IT t1, IT t2){ 
    if (t2 == IT.U.Instance){ return of(t1); }
    if (t1 == IT.U.Instance){ return of(t2); }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.rc().equals(x2.rc())){ return empty(); }
      if (!x1.c().name().equals(x2.c().name())){ return empty(); }
      return meet(x1.c().ts(),x2.c().ts()).map(ts->new IT.RCC(x1.rc(),new IT.C(x1.c().name(),ts)));
    }
    return t1.equals(t2) ? of(t1) : empty();
    }
  static Optional<List<IT>> meet(List<IT> t1, List<IT> t2){
    if (t1.size() != t2.size()){ return empty(); }
    var res= new ArrayList<IT>(t1.size());
    for(int i= 0; i<t1.size(); i++){
      var m= meet(t1.get(i),t2.get(i));
      if (m.isEmpty()){ return empty(); }
      res.add(m.get());
    }
    return of(Collections.unmodifiableList(res));
  }
  static boolean end(Data d){ return d.e().isEV(); }
  Data next(Data d){
    return d;
  }
}