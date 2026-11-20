package simplified;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

import utils.Join;
import utils.Streams;

final class Infer{
  enum Kind{ Lower, Upper, Eq, Ctx }
  record Src(T pattern, T actual, Kind kind){}
  final Map<String,E.L> decs;
  Infer(Map<String,E.L> decs){ this.decs= decs; }
  static String of(String src){
    var p= new Parser(src);
    var i= new Infer(p.decs);
    var res= p.top.stream().map(i::dec).toList();
    res.forEach(l -> i.check(l, Map.of()));
    return Join.of(res, "", "\n", "", "");
  }
  E dec(E e){
    var safe= norm(e, Map.of(), T.u);
    var res= pass(safe, Map.of(), T.u, true);
    return res.equals(safe) ? safe : dec(res);
  }
  E norm(E e, Map<String,T> g, T exp){
    var res= pass(e, g, exp, false);
    return res.equals(e) ? e : norm(res, g, exp);
  }
  E inner(E e, Map<String,T> g, T exp, boolean commit){ return commit ? pass(e, g, exp, true) : norm(e, g, exp); }
  Stream<T.C> supers(T.C c){
    var d= decs.get(c.name());
    var s= T.map(d.xs(), c.ts());
    return d.ts().stream().map(t -> (T.C)t.subst(s));
  }
  boolean sub(T a, T b){ return a.equals(b) || a instanceof T.C c && supers(c).anyMatch(s -> sub(s, b)); }
  Optional<T.C> up(T t, String n){
    if (!(t instanceof T.C c)){ return Optional.empty(); }
    return c.name().equals(n) ? Optional.of(c) : supers(c).flatMap(s -> up(s, n).stream()).findFirst();
  }
  static List<String> prime(List<String> xs){ return xs.stream().map(x -> x+"'").toList(); }
  Optional<M> sig(T.C t, String m){
    var d= decs.get(t.name());
    var sup= sig(supers(t), m);
    var own= d.ms().stream().filter(mi -> mi.name().equals(m)).findFirst().map(o -> o.rename(prime(o.xs())).subst(T.map(d.xs(), t.ts())));
    return own.map(o -> sup.map(s -> o.fill(s.rename(o.xs()))).orElse(o)).or(() -> sup);
  }
  Optional<M> sig(Stream<T.C> ts, String m){ return ts.flatMap(t -> sig(t, m).stream()).findFirst(); }
  M eff(M m, List<T> sups){ return sig(sups.stream().map(t -> (T.C)t), m.name()).map(s -> m.fill(s.rename(m.xs()))).orElse(m); }
  M sig(T.C t, E.Call c){
    var s= sig(t, c.m()).orElseThrow(() -> new Fail("Method \""+c.m()+"\" is not declared in type \""+t+"\""));
    if (s.ps().size() != c.es().size()){ throw new Fail("Method \""+c.m()+"\" of type \""+t+"\" has "+s.ps().size()+" parameters, but the call \""+c+"\" has "+c.es().size()+" arguments"); }
    var n= c.targs().map(List::size).orElse(s.xs().size());
    if (s.xs().size() != n){ throw new Fail("Method \""+c.m()+"\" of type \""+t+"\" has "+s.xs().size()+" type parameters, but the call \""+c+"\" has "+n+" type arguments"); }
    return s;
  }
  T type(E e){ return switch (e){
    case E.X(_, var t) -> t;
    case E.L l -> l.self();
    case E.Call c -> c.targs().isEmpty() || !(type(c.e()) instanceof T.C rt) ? T.u : inst(sig(rt, c), c.targs().get()).ret();
  };}
  static M inst(M s, List<T> targs){ return s.subst(T.map(s.xs(), targs)); }
  E pass(E e, Map<String,T> g, T exp, boolean commit){ return switch (e){
    case E.X(var x, var t) -> new E.X(x, t.fill(g.get(x)).fill(exp));
    case E.Call c -> call(c, g, exp, commit);
    case E.L l -> lit(l, g, exp, commit);
  };}
  E call(E.Call c, Map<String,T> g, T exp, boolean commit){
    var r= inner(c.e(), g, T.u, commit);
    if (!(type(r) instanceof T.C rt)){ return new E.Call(r, c.m(), c.targs(), c.es()); }
    var s= sig(rt, c);
    var targs= c.targs().orElse(Collections.nCopies(s.xs().size(), T.u));
    var es= Streams.zip(c.es(), inst(s, targs).ts()).map((e, t) -> inner(e, g, t, commit)).toList();
    var innerFirst= commit && !(r.equals(c.e()) && es.equals(c.es()));
    if (innerFirst){ return new E.Call(r, c.m(), Optional.of(targs), es); }
    var srcs= new ArrayList<Src>();
    Streams.zip(s.ts(), es).forEach((t, e) -> srcs.add(new Src(t, type(e), Kind.Lower)));
    srcs.add(new Src(s.ret(), exp, Kind.Ctx));
    return new E.Call(r, c.m(), Optional.of(decide(s.xs(), targs, srcs, commit)), es);
  }
  E lit(E.L l0, Map<String,T> g, T exp, boolean commit){
    var t= l0.t().fill(exp);
    var noHead= l0.anon() && l0.ts().isEmpty();
    var ts0= noHead && t instanceof T.C(var n, var as) ? List.<T>of(new T.C(n, Collections.nCopies(as.size(), T.u))) : l0.ts();
    var l= new E.L(l0.name(), l0.xs(), ts0, l0.ms(), t);
    var wait= l.anon() && ts0.isEmpty();
    if (wait){ return l; }
    var ms= l.ms().stream().map(m -> method(m, l, g, commit)).toList();
    var innerFirst= commit && !ms.equals(l.ms());
    var ts= l.anon() && !innerFirst ? List.of(head(l, ms, commit)) : l.ts();
    var done= ts.stream().allMatch(T::settled);
    return new E.L(l.name(), l.xs(), ts, done ? ms.stream().map(m -> eff(m, ts)).toList() : ms, t);
  }
  M method(M m, E.L l, Map<String,T> g, boolean commit){
    if (m.e().isEmpty()){ return m; }
    var eff= eff(m, l.ts());
    var g2= new HashMap<>(g);
    g2.put("this", l.self());
    Streams.zip(m.ps(), eff.ts()).forEach(g2::put);
    return new M(m.name(), m.xs(), m.ps(), m.ts(), m.ret(), Optional.of(inner(m.e().get(), g2, eff.ret(), commit)));
  }
  T head(E.L l, List<M> ms, boolean force){
    var head= (T.C)l.ts().getFirst();
    var xs= prime(decs.get(head.name()).xs());
    var pat= new T.C(head.name(), T.xs(xs));
    var srcs= new ArrayList<Src>();
    srcs.add(new Src(pat, l.t(), Kind.Ctx));
    ms.stream().filter(m -> m.e().isPresent()).forEach(m -> sig(pat, m.name()).ifPresent(s -> methodSrcs(m, s.rename(m.xs()), srcs)));
    return new T.C(head.name(), decide(xs, head.ts(), srcs, force));
  }
  void methodSrcs(M m, M s, ArrayList<Src> srcs){
    var body= m.e().get();
    Streams.zip(m.ts(), s.ts()).forEach((t, p) -> srcs.add(new Src(p, t, Kind.Eq)));
    Streams.zip(m.ps(), s.ts()).forEach((x, p) -> occ(x, body).forEach(o -> srcs.add(new Src(p, o, Kind.Upper))));
    srcs.add(new Src(s.ret(), m.ret(), Kind.Eq));
    srcs.add(new Src(s.ret(), type(body), Kind.Lower));
  }
  Stream<T> occ(String x, E e){ return switch (e){
    case E.X(var n, var t) -> n.equals(x) ? Stream.of(t) : Stream.of();
    case E.Call c -> Stream.concat(Stream.of(c.e()), c.es().stream()).flatMap(a -> occ(x, a));
    case E.L l -> l.ms().stream().flatMap(m -> m.e().stream()).flatMap(b -> occ(x, b));
  };}
  List<T> decide(List<String> xs, List<T> cur, List<Src> srcs, boolean force){
    return Streams.zip(xs, cur).map((x, t) -> decide(x, t, srcs, force)).toList();
  }
  T decide(String x, T cur, List<Src> all, boolean force){
    var srcs= all.stream().filter(s -> s.pattern().has(x)).toList();
    var exact= new ArrayList<T>();
    srcs.stream().filter(s -> !top(x, s)).forEach(s -> exact(x, s, exact));
    for (var e : exact){
      if (!cur.compatible(e)){ throw new Fail("The type argument \""+name(x)+"\" is required to be both \""+cur+"\" and \""+e+"\""); }
      cur = cur.fill(e);
    }
    if (cur.settled()){ return cur; }
    var ctx= bounds(x, srcs, Kind.Ctx);
    if (!ctx.isEmpty()){ return cur.fill(ctx.getFirst()); }
    var open= srcs.stream().anyMatch(s -> s.kind() != Kind.Eq && !s.actual().settled());
    var wait= open && !force;
    if (wait){ return cur; }
    var upper= bounds(x, srcs, Kind.Upper);
    if (!upper.isEmpty()){ return cur.fill(bottom(upper).orElseThrow(() -> disagree(x, upper, "subtype"))); }
    var lower= bounds(x, srcs, Kind.Lower);
    if (lower.isEmpty()){ return cur; }
    return cur.fill(top(lower).or(() -> top(lower.stream().map(this::widen).toList())).orElseThrow(() -> disagree(x, lower, "supertype")));
  }
  static boolean top(String x, Src s){ return s.kind() != Kind.Eq && s.pattern().equals(new T.X(x)); }
  static List<T> bounds(String x, List<Src> srcs, Kind k){
    return srcs.stream().filter(s -> s.kind() == k && top(x, s) && s.actual().settled()).map(Src::actual).toList();
  }
  static String name(String x){ return x.substring(0, x.length() - 1); }
  void exact(String x, Src s, ArrayList<T> out){
    switch (s.kind()){
      case Eq -> eq(x, s.pattern(), s.actual(), out);
      case Lower -> up(s.actual(), ((T.C)s.pattern()).name()).ifPresent(a -> eq(x, s.pattern(), a, out));
      case Upper, Ctx -> { if (s.actual() instanceof T.C a){ up(s.pattern(), a.name()).ifPresent(p -> eq(x, p, a, out)); } }
    }
  }
  void eq(String x, T p, T a, ArrayList<T> out){
    if (p.equals(new T.X(x))){ out.add(a); return; }
    if (!(p instanceof T.C(var n, var ps) && a instanceof T.C(var n2, var as) && n.equals(n2))){ return; }
    Streams.zip(ps, as).forEach((pi, ai) -> eq(x, pi, ai, out));
  }
  Fail disagree(String x, List<T> ts, String role){
    return new Fail("The type argument \""+name(x)+"\" is inferred from the types "+Join.of(ts.stream().distinct().map(t -> "\""+t+"\""), "", ", ", "", "")+", but no one of those types is a "+role+" of all the others");
  }
  Optional<T> top(List<T> ts){ return ts.stream().filter(t -> ts.stream().allMatch(o -> sub(o, t))).findFirst(); }
  Optional<T> bottom(List<T> ts){ return ts.stream().filter(t -> ts.stream().allMatch(o -> sub(t, o))).findFirst(); }
  T widen(T t){ return up(t, "WidenTo").map(w -> w.ts().getFirst()).orElse(t); }
  T check(E e, Map<String,T> g){ return switch (e){
    case E.X(var x, _) -> g.get(x);
    case E.Call c -> checkCall(c, g);
    case E.L l -> checkL(l, g);
  };}
  T checkCall(E.Call c, Map<String,T> g){
    if (!(check(c.e(), g) instanceof T.C rt)){ throw new Fail("The receiver of the call \""+c+"\" has a type parameter as its type, and a type parameter has no methods"); }
    var s= inst(sig(rt, c), c.targs().get());
    if (!c.targs().get().stream().allMatch(T::settled)){ throw new Fail("The type arguments of the call \""+c+"\" are not inferred"); }
    Streams.zip(c.es(), s.ts()).forEach((e, t) -> req(e, check(e, g), t));
    return s.ret();
  }
  void req(E e, T actual, T expected){
    if (!sub(actual, expected)){ throw new Fail("The expression \""+e+"\" has type \""+actual+"\", and \""+actual+"\" is not a subtype of \""+expected+"\""); }
  }
  T checkL(E.L l, Map<String,T> g){
    if (!(l.self() instanceof T.C self && self.settled())){ throw new Fail("The supertype of the literal \""+l+"\" is not inferred"); }
    l.ms().forEach(m -> checkM(m, l, g));
    return self;
  }
  void checkM(M m, E.L l, Map<String,T> g){
    if (!m.settled()){ throw new Fail("The signature of the method \""+m.name()+"\" of the literal \""+l+"\" is not inferred"); }
    if (m.e().isEmpty()){ return; }
    var g2= new HashMap<>(g);
    g2.put("this", l.self());
    Streams.zip(m.ps(), m.ts()).forEach(g2::put);
    req(m.e().get(), check(m.e().get(), g2), m.ret());
  }
}
