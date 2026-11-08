package fuzz;

import static java.util.stream.Collectors.joining;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fuzz.Ast.*;
import utils.Join;

final class Source{
  static final List<String> names= List.of(".m", ".n", "#");
  final HashMap<String,List<Meth>> signatures= new HashMap<>();
  final ArrayList<String> scope= new ArrayList<>();
  int fresh= 0;
  static String of(Program p){
    var s= new Source();
    return s.declaration("A", List.of(), p.a())+"\n"+s.declaration("B", List.of("A"), p.b())+"\n"+s.declaration("C", List.of("A", "B"), p.c())+"\n";
  }
  String declaration(String name, List<String> before, Dec d){
    var supers= IntStream.range(0, before.size()).filter(i -> d.supertypes() == Supers.both || d.supertypes().ordinal() == i+1).mapToObj(before::get).toList();
    var inherited= supers.stream().map(signatures::get).reduce(List.of(), (a, b) -> a.size() >= b.size() ? a : b);
    signatures.put(name, IntStream.range(0, Math.max(inherited.size(), d.methods().size())).mapToObj(i -> i < inherited.size() ? inherited.get(i) : d.methods().get(i)).toList());
    return name+":"+String.join(", ", supers)+"{ "+methods(d.methods(), inherited, true)+" }";
  }
  String methods(List<Meth> ms, List<Meth> inherited, boolean top){
    return IntStream.range(0, ms.size()).mapToObj(i -> method(i, ms.get(i), i < inherited.size() ? inherited.get(i) : null, top)).collect(joining("; "));
  }
  String method(int i, Meth m, Meth inherited, boolean top){
    var typed= m.typed() || inherited == null;
    var shape= typed ? m : inherited;
    var xs= shape.parameters().stream().map(_ -> "x"+(fresh++)).toList();
    var ps= IntStream.range(0, xs.size()).mapToObj(j -> typed ? xs.get(j)+": "+type(m.parameters().get(j)) : xs.get(j)).toList();
    var sig= (shape.rc() == Rc.iso ? "" : rc(shape.rc()))+names.get(i)+Join.of(ps, "(", ", ", ")", "")+(typed ? ": "+type(m.result()) : "");
    if (top && m.body() instanceof Abstract){ return sig; }
    var body= m.body() instanceof Returns(var e) ? e : new This();
    return sig+" -> "+scoped(xs, () -> expression(body));
  }
  String scoped(List<String> xs, Supplier<String> inside){
    scope.addAll(xs);
    try{ return inside.get(); }
    finally{ scope.subList(scope.size()-xs.size(), scope.size()).clear(); }
  }
  String expression(E e){ return switch (e){
    case This _ -> "this";
    case Parameter(var n) -> scope.isEmpty() ? "this" : scope.get(n.ordinal() % scope.size());
    case TypeName(var n) -> n;
    case Call(var r, var m, var rc, var args) -> expression(r)+names.get(m.ordinal())+(rc == Rc.none ? "" : "["+rc+"]")+Join.of(args.stream().map(this::expression), "(", ", ", ")", "");
    case Literal(var rc, var head, var ms) -> (head.isEmpty() ? "" : rc(rc)+head)+"{ "+methods(ms, signatures.getOrDefault(head, List.of()), false)+" }";
    case Function(var ps, var body) -> function(ps.stream().map(_ -> "x"+(fresh++)).toList(), body);
  };}
  String function(List<String> xs, E body){ return "{ "+String.join(", ", xs)+(xs.isEmpty() ? "" : " -> ")+scoped(xs, () -> expression(body))+" }"; }
  String type(Ty t){ return switch (t){
    case Named(var rc, var n) -> rc(rc)+n;
    case Lambda(var rc, var as, var r) -> rc(rc)+"base.F"+Join.of(Stream.concat(as.stream(), Stream.of(r)).map(this::type), "[", ",", "]", "");
  };}
  static String rc(Rc rc){ return rc == Rc.none ? "" : rc+" "; }
}
