package core;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import core.E.*;

public record AllLs(HashMap<TName,Literal> ls){
  public static Map<TName,Literal> of(List<Literal> tops){
    var all= new AllLs(new HashMap<>());
    tops.forEach(all::allLs);
    return Map.copyOf(all.ls);
  }
  void allLs(E e){
    if (e instanceof E.Literal l){ ls.put(l.name(),l); }
    e.children().forEach(this::allLs);
  }
}