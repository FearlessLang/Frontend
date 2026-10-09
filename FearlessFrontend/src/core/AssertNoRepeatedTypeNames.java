package core;
//assert by gpt unreviewd
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;

public final class AssertNoRepeatedTypeNames{
  private AssertNoRepeatedTypeNames(){}

  public static boolean ok(List<E.Literal> tops){
    var firstLit= new LinkedHashMap<TName,E.Literal>();
    var visited= Collections.newSetFromMap(new IdentityHashMap<E,Boolean>());
    tops.forEach(t->walk(t, firstLit, visited));
    return true;
  }
  private static void walk(E e, LinkedHashMap<TName,E.Literal> firstLit, Set<E> visited){
    if (!visited.add(e)){ return; }
    if (e instanceof E.Literal l){
      var prev= firstLit.putIfAbsent(l.name(), l);
      var duplicate= prev != null && prev != l;
      if (duplicate){
        throw new AssertionError(
          "Duplicate type name after inference: "+l.name().s()+" @"+l.name().arity()
          +"\n  first: "+prev.span()
          +"\n  again: "+l.span()
          +"\n  first infName="+prev.infName()+" again infName="+l.infName());
      }
    }
    e.children().forEach(c->walk(c, firstLit, visited));
  }
}