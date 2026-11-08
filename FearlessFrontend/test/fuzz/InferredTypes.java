package fuzz;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import core.FearlessException;
import tools.SourceOracle;
import utils.Join;

final class InferredTypes extends testUtils.FearlessTestBase{
  static final Pattern undeclared= Pattern.compile("Type \"([A-Z][A-Za-z0-9_]*)\" is not declared in package");
  static void check(Fuzz fuzz, String src){
    List<core.E.Literal> core;
    try{ core= compileAll("p", SourceOracle.debugBuilder().put(0, src).build(), fuzz.other); }
    catch (Throwable _){ return; }
    var targs= new Edits(src);
    core.stream().flatMap(InferredTypes::calls).forEach(targs::call);
    var heads= new Edits(src);
    core.stream().flatMap(InferredTypes::literals).forEach(l -> heads.literal(l, false));
    var sigs= new Edits(src);
    core.stream().flatMap(InferredTypes::literals).forEach(l -> sigs.literal(l, true));
    rewrite(fuzz, src, core, targs, "the inferred type arguments");
    rewrite(fuzz, src, core, heads, "the inferred heads of object literals");
    rewrite(fuzz, src, core, sigs, "the inferred heads and method signatures of object literals");
  }
  static void rewrite(Fuzz fuzz, String src, List<core.E.Literal> core, Edits edits, String what){
    edits.text.keySet().removeAll(edits.bad);
    var written= src;
    var got= "";
    while (true){
      if (edits.text.isEmpty()){ return; }
      written = edits.apply();
      var o= SourceOracle.debugBuilder().put(0, written).build();
      try{ got = canon(lines(compileAll("p", o, fuzz.other))); }
      catch (FearlessException fe){ got = "rejected: "+fe.render(o); }
      catch (Throwable t){ got = "crashes: "+Fuzz.crash(t); }
      var m= undeclared.matcher(got);
      if (!m.find()){ break; }
      var x= Pattern.compile("(^|[^A-Za-z0-9_])"+m.group(1)+"($|[^A-Za-z0-9_])");
      if (!edits.text.values().removeIf(t -> x.matcher(t).find())){ break; }
    }
    var expected= canon(lines(core));
    var kind= got.startsWith("rejected: ") ? "rejected after writing "+what
      : got.startsWith("crashes: ") ? "crash after writing "+what+": "+got.substring("crashes: ".length())
      : got.equals(expected) ? "" : "different core after writing "+what;
    if (!kind.isEmpty()){ fuzz.found(kind, src+"\n---- written as ----\n"+written+"\n---- gives ----\n"+got+"\n---- instead of ----\n"+expected); }
    fuzz.check(written);
  }
  static Stream<core.E.Call> calls(core.E e){
    var here= e instanceof core.E.Call c ? Stream.of(c) : Stream.<core.E.Call>of();
    return Stream.concat(here, e.children().flatMap(InferredTypes::calls));
  }
  static Stream<core.E.Literal> literals(core.E e){
    var here= e instanceof core.E.Literal l ? Stream.of(l) : Stream.<core.E.Literal>of();
    return Stream.concat(here, e.children().flatMap(InferredTypes::literals));
  }
  static boolean fresh(fearlessFullGrammar.E e){ return e instanceof fearlessFullGrammar.E.Call c ? fresh(c.e()) : e instanceof fearlessFullGrammar.E.X x && x.name().startsWith("_"); }
  static final class Edits{
    final String src;
    final TreeMap<Integer,String> text= new TreeMap<>();
    final HashSet<Integer> bad= new HashSet<>();
    final Map<String,String> aliases;
    Edits(String src){ this.src= src; aliases= uses.matcher(src).results().collect(Collectors.toMap(m -> m.group(1), m -> m.group(2))); }
    static final Pattern uses= Pattern.compile("use ([a-z][a-z0-9_]*\\.\\w+) as (\\w+);");
    String written(core.T t){ return switch (t){
      case core.T.X x -> x.name();
      case core.T.RCX(var rc, var x) -> rc.name()+" "+x.name();
      case core.T.ReadImmX(var x) -> "read/imm "+x.name();
      case core.T.RCC(var rc, var c, _) -> rc.name()+" "+written(c);
    };}
    String written(core.T.C c){
      var n= aliases.getOrDefault(c.name().s(), c.name().pkgName().equals("p") ? c.name().simpleName() : c.name().s());
      return n+Join.of(c.ts().stream().map(this::written), "[", ",", "]", "");
    }
    String apply(){
      var res= src;
      for (var e : text.descendingMap().entrySet()){ res = Mutations.insert(res, e.getKey(), e.getValue()); }
      return res;
    }
    void add(int at, String t){
      if (at < 0){ return; }
      var old= text.putIfAbsent(at, t);
      var unwritable= Pattern.compile("(^|[^A-Za-z0-9])_").matcher(t).find();
      if (unwritable || (old != null && !old.equals(t))){ bad.add(at); }
    }
    void call(core.E.Call c){
      if (!(c.src().inner instanceof fearlessFullGrammar.E.Call sc) || sc.targs().isPresent() || !sc.name().s().equals(c.name().s()) || fresh(sc.e())){ return; }
      var ts= Join.of(Stream.concat(Stream.of(c.rc().name()), c.targs().stream().map(this::written)), "[", ",", "]", "");
      add(nameEnd(sc.pos().line(), sc.pos().column(), c.name().s()), ts);
    }
    void literal(core.E.Literal l, boolean sigs){
      if (l.src().inner instanceof fearlessFullGrammar.E.Literal sl && l.infName() && !l.cs().isEmpty()){
        var at= offset(sl.span().inner.startLine(), sl.span().inner.startCol());
        add(src.startsWith("{", at) ? at : src.startsWith("{", at+1) ? at+1 : -1, " "+l.rc().name()+" "+written(l.cs().getFirst()));
      }
      if (!sigs){ return; }
      var ms= switch (l.src().inner){
        case fearlessFullGrammar.E.Literal sl -> sl.methods();
        case fearlessFullGrammar.E.TypedLiteral tl -> tl.l().map(fearlessFullGrammar.E.Literal::methods).orElse(List.of());
        default -> List.<fearlessFullGrammar.M>of();
      };
      for (var sm : ms){ l.ms().stream().filter(cm -> cm.sig().span().inner.equals(sm.span().inner)).findFirst().ifPresent(cm -> method(sm, cm.sig())); }
    }
    void method(fearlessFullGrammar.M sm, core.Sig s){
      if (sm.sig().isEmpty() || sm.body().isEmpty() || !sm.sig().get().hasParenthesis() || sm.sig().get().m().isEmpty()){ return; }
      var ps= sm.sig().get().parameters();
      if (ps.size() != s.ts().size()){ return; }
      for (int i= 0; i < ps.size(); i += 1){
        if (ps.get(i).t().isPresent() || !(ps.get(i).xp().orElse(null) instanceof fearlessFullGrammar.XPat.Name(var x))){ continue; }
        add(nameEnd(x.pos().line(), x.pos().column(), x.name()), ": "+written(s.ts().get(i)));
      }
      if (sm.sig().get().t().isPresent()){ return; }
      var open= src.indexOf('(', offset(sm.span().inner.startLine(), sm.span().inner.startCol()));
      var close= open < 0 ? -1 : src.indexOf(')', open);
      if (close >= 0){ add(close+1, ": "+written(s.ret())); }
    }
    int offset(int line, int column){
      var start= 0;
      for (int i= 1; i < line; i += 1){ start = src.indexOf('\n', start) + 1; }
      return start+column-1;
    }
    int nameEnd(int line, int column, String name){
      for (var at : List.of(offset(line, column), offset(line, column)+1)){
        var end= at+name.length();
        if (at >= 0 && src.startsWith(name, at) && !src.substring(end).matches("(?s)[A-Za-z0-9_'].*")){ return end; }
      }
      return -1;
    }
  }
}
