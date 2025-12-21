package typeSystem;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import core.E;
import core.M;
import core.TName;
import core.E.*;

public record AllLs(HashMap<TName,Literal> ls) {
  static public Map<TName,Literal> of(List<Literal> tops){
    var all= new AllLs(new HashMap<>());
    tops.forEach(all::allLs);
    return Map.copyOf(all.ls);
  }
  void allLs(E e){ switch (e){
    case E.X _ -> {}
    case E.Type _ -> {}
    case E.Literal l ->{ ls.put(l.name(),l); l.ms().forEach(this::allLs); }
    case E.Call(var r, _, _, _, var es, _,_) ->{allLs(r); es.forEach(this::allLs); } 
  };}
  void allLs(M m){ m.e().ifPresent(this::allLs); }
}