package fuzz;

import static java.util.stream.Collectors.joining;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Supplier;
import java.util.regex.Pattern;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fuzz.Ast.*;
import utils.Join;

final class Source{
  static final List<String> names= List.of(".m", ".n", "#", ".k");
  static final List<String> declarations= List.of("A", "B", "C", "D");
  static final String helpers= """
    Id:{ #[Y:**](y: Y): Y -> y }
    Box[X:**]:{ .m: X; .n(x: X): Box[X]; #: Box[X] }
    """;
  final HashMap<String,List<Meth>> signatures= new HashMap<>();
  final HashMap<String,List<String>> supertypes= new HashMap<>();
  final HashMap<String,Set<Integer>> abstracts= new HashMap<>();
  final ArrayList<String> scope= new ArrayList<>();
  final ArrayList<String> scopeTypes= new ArrayList<>();
  String declaring= "";
  final ArrayList<String> generics= new ArrayList<>();
  final ArrayList<String> selves= new ArrayList<>();
  final ArrayList<String> selfTypes= new ArrayList<>();
  int fresh= 0;
  static String of(Program p){
    var s= new Source();
    declarations.forEach(s::box);
    s.bases();
    var ds= List.of(p.a(), p.b(), p.c(), p.d());
    return helpers+IntStream.range(0, ds.size()).mapToObj(i -> s.declaration(declarations.get(i), declarations.subList(0, i), ds.get(i))+"\n").collect(joining());
  }
  final HashMap<String,List<String>> methodNames= new HashMap<>();
  static final List<String> values= List.of("base.Void", "base.True", "base.False", "5");
  void bases(){
    var bool= new Named(Rc.none, "base.Bool");
    var nat= new Named(Rc.none, "base.Nat");
    var bools= List.of(sig(bool), sig(bool, bool), sig(bool, bool), sig(bool, bool));
    var nats= List.of(sig(nat, nat), sig(nat, nat));
    base("base.Bool", List.of(".not", ".and", ".or", "&"), bools, List.of(), Set.of(0));
    base("base.True", List.of(".not", ".and", ".or", "&"), bools, List.of("base.Bool"), Set.of());
    base("base.False", List.of(".not", ".and", ".or", "&"), bools, List.of("base.Bool"), Set.of());
    base("base.Nat", List.of(" +", " *"), nats, List.of(), Set.of(0));
    base("5", List.of(" +", " *"), nats, List.of("base.Nat"), Set.of());
    supertypes.put("base.Void", List.of());
    abstracts.put("base.Void", Set.of());
  }
  void base(String type, List<String> names, List<Meth> methods, List<String> supers, Set<Integer> open){
    methodNames.put(type, names);
    signatures.put(type, methods);
    supertypes.put(type, supers);
    abstracts.put(type, open);
  }
  static Meth sig(Named result, Named... parameters){ return new Meth(Rc.none, true, false, List.of(parameters), result, new Abstract()); }
  String methodName(String type, int method){
    var ns= methodNames.getOrDefault(type, names);
    return ns.get(method % ns.size());
  }
  int methodIndex(String type, int method){ return methodNames.containsKey(type) ? method % methodNames.get(type).size() : method; }
  void box(String x){
    var name= "Box["+x+"]";
    var t= new Named(Rc.none, x);
    var self= new Named(Rc.none, name);
    signatures.put(name, List.of(new Meth(Rc.none, true, false, List.of(), t, new Abstract()), new Meth(Rc.none, true, false, List.of(t), self, new Abstract()), new Meth(Rc.none, true, false, List.of(), self, new Abstract())));
    abstracts.put(name, Set.of(0, 1, 2));
  }
  String declaration(String name, List<String> before, Dec written){
    var d= Trees.map(written, v -> v instanceof Named(var rc, var n) && n.contains("Self") ? new Named(rc, n.replace("Self", name)) : v);
    var boxes= d.boxes().stream().map(b -> b.replace("Self", name));
    var earlier= before.isEmpty() ? Stream.<String>empty() : d.supertypes().stream().map(n -> before.get(n.ordinal() % before.size()));
    var supers= Stream.concat(earlier, boxes).distinct().toList();
    var inherited= supers.stream().map(signatures::get).reduce(List.of(), (a, b) -> a.size() >= b.size() ? a : b);
    signatures.put(name, IntStream.range(0, Math.max(inherited.size(), d.methods().size())).mapToObj(i -> i < inherited.size() ? inherited.get(i) : d.methods().get(i)).toList());
    supertypes.put(name, supers);
    var open= new TreeSet<Integer>();
    supers.forEach(s -> open.addAll(abstracts.get(s)));
    IntStream.range(0, d.methods().size()).forEach(i -> { if (d.methods().get(i).body() instanceof Abstract){ open.add(i); } else { open.remove(i); } });
    abstracts.put(name, open);
    declaring= name;
    return name+":"+String.join(", ", supers)+"{ "+methods(d.methods(), inherited, true)+" }";
  }
  String methods(List<Meth> ms, List<Meth> inherited, boolean top){
    return IntStream.range(0, ms.size()).mapToObj(i -> method(i, ms.get(i), i < inherited.size() ? inherited.get(i) : null, top)).collect(joining("; "));
  }
  String method(int i, Meth m, Meth inherited, boolean top){
    var typed= m.typed() || inherited == null;
    var shape= typed ? m : inherited;
    var xs= shape.parameters().stream().map(_ -> "x"+(fresh++)).toList();
    var generic= typed && m.generic();
    if (generic){ generics.add("X"+(generics.size()+1)); }
    try{ return method(i, m, typed, shape, xs, generic, top); }
    finally{ if (generic){ generics.removeLast(); } }
  }
  String method(int i, Meth m, boolean typed, Meth shape, List<String> xs, boolean generic, boolean top){
    var ps= IntStream.range(0, xs.size()).mapToObj(j -> typed ? xs.get(j)+": "+type(m.parameters().get(j)) : xs.get(j)).toList();
    var sig= methodRc(shape.rc())+names.get(i)+(generic ? "["+generics.getLast()+"]" : "")+Join.of(ps, "(", ", ", ")", "")+(typed ? ": "+type(m.result()) : "");
    if (top && m.body() instanceof Abstract){ return sig; }
    var body= m.body() instanceof Returns(var e) ? e : new This();
    var types= shape.parameters().stream().map(Source::name).toList();
    return sig+" -> "+scoped(xs, types, () -> body(body, shape.result()));
  }
  String body(E e, Ty expected){
    var got= typeOf(e);
    var fits= got != null && name(expected) != null && subtype(got, name(expected));
    var leaf= e instanceof This || e instanceof Parameter || e instanceof TypeName;
    if (fits || got == null && !leaf){ return expression(e); }
    var v= value(expected);
    return v == null ? expression(e) : v;
  }
  String value(Ty t){ return switch (t){
    case Named(_, var n) -> Stream.concat(values.stream(), declarations.stream()).filter(d -> abstracts.containsKey(d) && abstracts.get(d).isEmpty() && subtype(d, n)).findFirst().orElse(null);
    case Lambda(_, var as, var r) -> functionReturning(as.size(), value(r));
  };}
  String functionReturning(int arity, String result){
    if (result == null){ return null; }
    var xs= IntStream.range(0, arity).mapToObj(_ -> "x"+(fresh++)).toList();
    return "{ "+String.join(", ", xs)+(xs.isEmpty() ? "" : " -> ")+result+" }";
  }
  boolean subtype(String a, String b){ return a.equals(b) || supertypes.getOrDefault(a, List.of()).stream().anyMatch(s -> subtype(s, b)); }
  String typeOf(E e){ return switch (e){
    case This _ -> selves.isEmpty() ? declaring : selfTypes.getLast();
    case Parameter(var n) -> scope.isEmpty() ? declaring : scopeTypes.get(scope.size()-1-n.ordinal() % scope.size());
    case TypeName(var n) -> n;
    case Call(var r, var m, _, _) -> resultOf(typeOf(r), m.ordinal());
    case Literal(_, var head, _, _) -> head.isEmpty() ? null : head;
    default -> null;
  };}
  String resultOf(String type, int method){
    var m= signatureOf(type, method);
    return m == null ? null : name(m.result());
  }
  Meth signatureOf(String type, int method){
    if (type == null || !signatures.containsKey(type) || methodIndex(type, method) >= signatures.get(type).size()){ return null; }
    return signatures.get(type).get(methodIndex(type, method));
  }
  String arguments(E receiver, Nth method, List<E> args){
    var m= signatureOf(typeOf(receiver), method.ordinal());
    if (m == null){ return Join.of(args.stream().map(this::expression), "(", ", ", ")", ""); }
    var ps= m.parameters();
    return Join.of(IntStream.range(0, ps.size()).mapToObj(i -> i < args.size() ? body(args.get(i), ps.get(i)) : value(ps.get(i))).map(a -> a == null ? "this" : a), "(", ", ", ")", "");
  }
  static String name(Ty t){ return t instanceof Named(_, var n) ? n : null; }
  String scoped(List<String> xs, Supplier<String> inside){ return scoped(xs, xs.stream().map(_ -> (String)null).toList(), inside); }
  String scoped(List<String> xs, List<String> types, Supplier<String> inside){
    scope.addAll(xs);
    scopeTypes.addAll(types);
    try{ return inside.get(); }
    finally{
      scope.subList(scope.size()-xs.size(), scope.size()).clear();
      scopeTypes.subList(scopeTypes.size()-xs.size(), scopeTypes.size()).clear();
    }
  }
  String expression(E e){ return switch (e){
    case This _ -> selves.isEmpty() ? "this" : selves.getLast();
    case Parameter(var n) -> scope.isEmpty() ? "this" : scope.get(scope.size()-1-n.ordinal() % scope.size());
    case TypeName(var n) -> n;
    case Call(var r, var m, var rc, var args) -> expression(r)+methodName(typeOf(r), m.ordinal())+(valueRc(rc).isEmpty() ? "" : "["+rc+"]")+arguments(r, m, args);
    case Literal(var rc, var head, var self, var ms) -> literal(head.isEmpty() ? "" : valueRc(rc)+head, self ? List.of("s"+(fresh++)) : List.of(), head.isEmpty() ? null : head, ms, signatures.getOrDefault(head, List.of()));
    case Declared(var rc, var sup, var ms) -> literal(valueRc(rc)+"D"+(fresh++)+":"+sup, List.of(), null, ms, signatures.getOrDefault(sup, List.of()));
    case Function(var ps, var body) -> function(ps.stream().map(_ -> "x"+(fresh++)).toList(), body);
  };}
  String literal(String head, List<String> self, String selfType, List<Meth> ms, List<Meth> inherited){
    selves.addAll(self);
    selfTypes.addAll(self.stream().map(_ -> selfType).toList());
    String body;
    try{ body= scoped(self, self.stream().map(_ -> selfType).toList(), () -> methods(ms, inherited, false)); }
    finally{
      selves.subList(selves.size()-self.size(), selves.size()).clear();
      selfTypes.subList(selfTypes.size()-self.size(), selfTypes.size()).clear();
    }
    var completed= abstracts.getOrDefault(selfType, Set.of()).stream().filter(i -> i >= ms.size()).map(i -> completion(i, inherited.get(i))).filter(c -> c != null).toList();
    var all= Stream.concat(Stream.of(body).filter(b -> !b.isEmpty()), completed.stream()).collect(joining("; "));
    var used= self.stream().filter(x -> Pattern.compile("\\b"+x+"\\b").matcher(all).find()).map(x -> "'"+x+" ").collect(joining());
    return head+"{ "+used+all+" }";
  }
  String completion(int i, Meth inherited){
    var v= value(inherited.result());
    if (v == null){ return null; }
    var xs= inherited.parameters().stream().map(_ -> "x"+(fresh++)).toList();
    return methodRc(inherited.rc())+names.get(i)+Join.of(xs, "(", ", ", ")", "")+" -> "+v;
  }
  String function(List<String> xs, E body){ return "{ "+String.join(", ", xs)+(xs.isEmpty() ? "" : " -> ")+scoped(xs, () -> expression(body))+" }"; }
  String type(Ty t){ return switch (t){
    case Named(var rc, var n) -> rc(rc)+(!n.equals("X") ? n : generics.isEmpty() ? declaring : generics.getLast());
    case Lambda(var rc, var as, var r) -> rc(rc)+"base.F"+Join.of(Stream.concat(as.stream(), Stream.of(r)).map(this::type), "[", ",", "]", "");
  };}
  static String rc(Rc rc){ return rc == Rc.none ? "" : rc+" "; }
  static String valueRc(Rc rc){ return rc == Rc.readH || rc == Rc.mutH ? "" : rc(rc); }
  static String methodRc(Rc rc){ return rc == Rc.imm || rc == Rc.read || rc == Rc.mut ? rc+" " : ""; }
}
