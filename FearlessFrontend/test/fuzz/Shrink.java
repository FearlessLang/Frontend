package fuzz;

import java.lang.reflect.AnnotatedType;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.Predicate;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fuzz.Gen.OneOf;

final class Shrink{
  static final int attempts= 2000;
  static final Pattern token= Pattern.compile("^\\s+|\\w+\\s*|\\S\\s*");
  static Predicate<String> budget(Predicate<String> keeps){
    var left= new int[]{attempts};
    return s -> left[0]-- > 0 && keeps.test(s);
  }
  static String text(String src, Predicate<String> keeps){
    var tries= budget(keeps);
    var ts= token.matcher(src).results().map(MatchResult::group).toList();
    for (int chunk= Math.max(1, ts.size()/2); chunk >= 1; chunk /= 2){
      for (int i= 0; i+chunk <= ts.size();){
        var shorter= Stream.concat(ts.subList(0, i).stream(), ts.subList(i+chunk, ts.size()).stream()).toList();
        if (tries.test(String.join("", shorter))){ ts= shorter; }
        else { i += chunk; }
      }
    }
    return String.join("", ts);
  }
  static Ast.Program tree(Ast.Program p, Predicate<String> keeps){
    var tries= budget(keeps);
    for (int k= 0; k < Trees.positions(p); k += 1){
      var smaller= smaller(p, k).stream().filter(c -> tries.test(Source.of(c))).findFirst();
      if (smaller.isPresent()){ p= smaller.get(); k= -1; }
    }
    return p;
  }
  static List<Ast.Program> smaller(Ast.Program p, int k){
    var here= new ArrayList<Object>();
    Trees.replace(p, k, (v, t) -> { here.add(v); here.add(t); return v; });
    return smaller(here.get(0), (AnnotatedType)here.get(1)).stream().map(s -> Trees.replace(p, k, (_, _) -> s)).toList();
  }
  static List<Object> smaller(Object v, AnnotatedType t){
    if (v instanceof List<?> l){ return IntStream.range(0, l.size()).mapToObj(i -> (Object)Stream.concat(l.subList(0, i).stream(), l.subList(i+1, l.size()).stream()).toList()).toList(); }
    if (v instanceof Boolean b){ return b ? List.of(false) : List.of(); }
    if (v instanceof Enum<?> e){ return e.ordinal() == 0 ? List.of() : List.of(e.getDeclaringClass().getEnumConstants()[0]); }
    if (v instanceof String s){ var first= t.getAnnotation(OneOf.class).value()[0]; return s.equals(first) ? List.of() : List.of(first); }
    if (!(t.getType() instanceof Class<?> c) || !c.isSealed()){ return List.of(); }
    var res= new ArrayList<Object>(descendants(v, c));
    if (!Gen.leaf(v.getClass())){ res.add(new Gen(new Random(0), 0).value(t)); }
    return res;
  }
  static List<Object> descendants(Object v, Class<?> c){
    if (v instanceof List<?> l){ return l.stream().flatMap(x -> withDescendants(x, c).stream()).toList(); }
    if (!v.getClass().isRecord()){ return List.of(); }
    return Stream.of(v.getClass().getRecordComponents()).flatMap(rc -> withDescendants(Trees.get(rc, v), c).stream()).toList();
  }
  static List<Object> withDescendants(Object v, Class<?> c){ return Stream.concat(Stream.of(v).filter(c::isInstance), descendants(v, c).stream()).toList(); }
}
