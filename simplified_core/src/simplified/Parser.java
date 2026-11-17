package simplified;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;
import java.util.regex.Pattern;

final class Parser{
  static final Pattern token= Pattern.compile("\\s*(->|[A-Za-z_][A-Za-z0-9_]*|[\\[\\](){}:,;.?])");
  final ArrayList<String> toks= new ArrayList<>();
  final LinkedHashMap<String,E.L> decs= new LinkedHashMap<>();
  final ArrayList<E.L> top= new ArrayList<>();
  final ArrayList<T.C> cs= new ArrayList<>();
  int i= 0;
  Parser(String src){
    var s= "WidenTo[T]:{}"+src.strip();
    var m= token.matcher(s);
    var end= 0;
    while (end < s.length()){
      if (!m.region(end, s.length()).lookingAt()){ throw new Fail("Unexpected character \""+s.charAt(end)+"\""); }
      toks.add(m.group(1));
      end = m.end();
    }
    while (i < toks.size()){ top.add(lit(Set.of(), Set.of())); }
    cs.forEach(this::wf);
  }
  void wf(T.C c){
    var d= decs.get(c.name());
    if (d == null){ throw new Fail("Type name \""+c.name()+"\" is not declared"); }
    if (d.xs().size() != c.ts().size()){ throw new Fail("Type \""+c+"\" has "+c.ts().size()+" type arguments, but \""+d.self()+"\" is declared with "+d.xs().size()); }
  }
  String peek(){ return i < toks.size() ? toks.get(i) : ""; }
  boolean eat(String t){
    if (!peek().equals(t)){ return false; }
    i += 1;
    return true;
  }
  void req(String t){ if (!eat(t)){ throw new Fail("Expected \""+t+"\" but found \""+peek()+"\""); } }
  boolean upper(){ return !peek().isEmpty() && Character.isUpperCase(peek().charAt(0)); }
  String id(boolean upper){
    var t= peek();
    var ok= !t.isEmpty() && Character.isJavaIdentifierStart(t.charAt(0)) && upper() == upper;
    if (!ok){ throw new Fail("Expected "+(upper ? "a type name" : "a method or variable name")+" but found \""+t+"\""); }
    i += 1;
    return t;
  }
  <R> List<R> list(String open, String close, Supplier<R> elem){
    if (!eat(open)){ return List.of(); }
    var res= new ArrayList<R>();
    while (!eat(close)){
      if (!res.isEmpty()){ req(","); }
      res.add(elem.get());
    }
    return List.copyOf(res);
  }
  List<String> xs(Set<String> scope){
    var res= list("[", "]", () -> id(true));
    var all= new HashSet<>(scope);
    res.forEach(x -> { if (!all.add(x)){ throw new Fail("Type parameter \""+x+"\" is declared twice"); } });
    return res;
  }
  T type(Set<String> xs){
    var n= id(true);
    if (xs.contains(n)){ return new T.X(n); }
    var c= new T.C(n, list("[", "]", () -> type(xs)));
    cs.add(c);
    return c;
  }
  T sType(Set<String> xs){ return eat("?") ? T.u : type(xs); }
  E.L lit(Set<String> xs, Set<String> vs){
    if (!upper()){ return new E.L("", List.of(), List.of(), ms(xs, vs), T.u); }
    var n= id(true);
    var own= xs(Set.of());
    var inner= Set.copyOf(own);
    req(":");
    var ts= new ArrayList<T>();
    while (!peek().equals("{")){
      if (!ts.isEmpty()){ req(","); }
      var t= type(inner);
      if (!(t instanceof T.C)){ throw new Fail("Type \""+n+"\" has the type parameter \""+t+"\" as a supertype"); }
      ts.add(t);
    }
    var l= new E.L(n, own, List.copyOf(ts), ms(inner, vs), T.u);
    if (decs.put(n, l) != null){ throw new Fail("Type name \""+n+"\" is declared twice"); }
    return l;
  }
  List<M> ms(Set<String> xs, Set<String> vs){
    req("{");
    var res= new ArrayList<M>();
    while (!eat("}")){
      var m= m(xs, vs);
      var twice= res.stream().anyMatch(mi -> mi.name().equals(m.name()));
      if (twice){ throw new Fail("Method \""+m.name()+"\" is declared twice in the same literal"); }
      res.add(m);
    }
    return List.copyOf(res);
  }
  M m(Set<String> xs, Set<String> vs){
    var n= id(false);
    var own= xs(xs);
    var inner= new HashSet<>(xs);
    inner.addAll(own);
    var ps= new ArrayList<String>();
    var ts= new ArrayList<T>();
    var inVs= new HashSet<>(vs);
    inVs.remove("this");
    req("(");
    while (!eat(")")){
      if (!ps.isEmpty()){ req(","); }
      var p= id(false);
      if (!inVs.add(p)){ throw new Fail("Variable \""+p+"\" is declared twice"); }
      ps.add(p);
      req(":");
      ts.add(sType(inner));
    }
    inVs.add("this");
    req(":");
    var m= new M(n, own, List.copyOf(ps), List.copyOf(ts), sType(inner), Optional.empty());
    if (eat(";")){
      if (!m.settled()){ throw new Fail("Method \""+m+"\" has no body and has \"?\" in the signature; only a method with a body can have \"?\" in the signature"); }
      return m;
    }
    req("->");
    var res= new M(n, own, m.ps(), m.ts(), m.ret(), Optional.of(e(inner, inVs)));
    req(";");
    return res;
  }
  E e(Set<String> xs, Set<String> vs){
    var res= atom(xs, vs);
    while (eat(".")){
      var m= id(false);
      Optional<List<T>> targs= peek().equals("[") ? Optional.of(list("[", "]", () -> type(xs))) : Optional.empty();
      if (!peek().equals("(")){ throw new Fail("Expected \"(\" but found \""+peek()+"\""); }
      res = new E.Call(res, m, targs, list("(", ")", () -> e(xs, vs)));
    }
    return res;
  }
  E atom(Set<String> xs, Set<String> vs){
    if (upper() || peek().equals("{")){ return lit(xs, vs); }
    var x= id(false);
    if (!vs.contains(x)){ throw new Fail("Variable \""+x+"\" is not declared"); }
    return new E.X(x, T.u);
  }
}
