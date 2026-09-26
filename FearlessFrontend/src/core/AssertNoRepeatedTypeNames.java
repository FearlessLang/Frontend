package core;
//assert by gpt unreviewd
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class AssertNoRepeatedTypeNames{
  private AssertNoRepeatedTypeNames(){}

  public static boolean ok(List<E.Literal> tops){
    var firstLit= new LinkedHashMap<TName,E.Literal>();
    var visited= Collections.newSetFromMap(new IdentityHashMap<E,Boolean>());
    tops.forEach(t->walk(t, firstLit, visited));
    return true;
  }
  private static void walk(E e, Map<TName,E.Literal> firstLit, Set<E> visited){
    if (!visited.add(e)){ return; }
    switch (e){
      case E.X _, E.Type _ -> {}
      case E.Call c -> { walk(c.e(), firstLit, visited); c.es().forEach(a->walk(a, firstLit, visited)); }
      case E.Literal l -> {
        var prev= firstLit.putIfAbsent(l.name(), l);
        var duplicate= prev != null && prev != l;
        if (duplicate){
          throw new AssertionError(
            "Duplicate type name after inference: "+l.name().s()+" @"+l.name().arity()
            +"\n  first: "+prev.span()
            +"\n  again: "+l.span()
            +"\n  first infName="+prev.infName()+" again infName="+l.infName());
        }
        l.ms().forEach(m->m.e().ifPresent(body->walk(body, firstLit, visited)));
      }
    }
  }
}