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
    var firstLit=new LinkedHashMap<TName,E.Literal>();
    var firstSpan=new LinkedHashMap<TName,TSpan>();
    var visited= Collections.newSetFromMap(new IdentityHashMap<E,Boolean>());
    tops.forEach(t->walk(t, firstLit, firstSpan, visited));
    return true;
  }
  private static void walk(E e, Map<TName,E.Literal> firstLit, Map<TName,TSpan> firstSpan, Set<E> visited){
    if (!visited.add(e)) return;
    switch(e){
      case E.X _ -> {}
      case E.Type _ -> {}
      case E.Call c -> { walk(c.e(), firstLit, firstSpan, visited); c.es().forEach(a->walk(a, firstLit, firstSpan, visited)); }
      case E.Literal l -> {
        var prev= firstLit.putIfAbsent(l.name(), l);
        if (prev != null && prev != l){
          var a= firstSpan.get(l.name());
          var b= l.span();
          throw new AssertionError(
            "Duplicate type name after inference: "+l.name().s()+" @"+l.name().arity()
            +"\n  first: "+a
            +"\n  again: "+b
            +"\n  first infName="+prev.infName()+" again infName="+l.infName());
        }
        firstSpan.putIfAbsent(l.name(), l.span());
        l.ms().forEach(m->m.e().ifPresent(body->walk(body, firstLit, firstSpan, visited)));
      }
    }
  }
}