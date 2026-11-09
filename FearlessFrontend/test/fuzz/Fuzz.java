package fuzz;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.FearlessException;
import core.OtherPackages;
import testUtils.DbgBlock;
import tools.SourceOracle;
import utils.Join;

final class Fuzz extends testUtils.FearlessTestBase{
  final OtherPackages other;
  final List<compact.Frontend.Literal> compactOther;
  final SourceOracle fallback;
  final String name;
  final TreeMap<String,String> found= new TreeMap<>();
  final TreeMap<String,Integer> rejections= new TreeMap<>();
  final HashSet<String> triples= new HashSet<>();
  int checked= 0;
  Fuzz(String name){ this(name, otherFrom(DbgBlock.all()), checkCompact ? compactBase() : List.of(), DbgBlock.dbgMiniBase()); }
  Fuzz(String name, OtherPackages other, List<compact.Frontend.Literal> compactOther, SourceOracle fallback){
    this.name= name;
    this.other= other;
    this.compactOther= compactOther;
    this.fallback= fallback;
  }
  void found(String key, String program){ found.merge(key, program, (a, b) -> a.length() <= b.length() ? a : b); }
  void assertNothingFound(){
    System.out.println(summary());
    strCmp("", Join.of(found.entrySet().stream().map(e -> e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
  }
  String summary(){
    var rejected= rejections.values().stream().mapToInt(i -> i).sum();
    var frequent= rejections.entrySet().stream().sorted(Map.Entry.<String,Integer>comparingByValue().reversed()).limit(3).map(e -> e.getKey()+" "+e.getValue());
    return name+": "+checked+" programs, "+(checked-rejected)+" accepted by the full frontend, "+triples.size()+" triples of core tokens; most frequent rejections: "+Join.of(frequent, "", ", ", "", "");
  }
  record Outcome(String rejection, String finding, String core){ boolean accepted(){ return rejection.isEmpty(); } }
  boolean check(String src){ return record(src, outcome(src), finding -> Shrink.text(src, same(finding))) >= 0; }
  void check(List<String> srcs){
    var outcomes= srcs.parallelStream().map(this::outcome).toList();
    IntStream.range(0, srcs.size()).forEach(i -> record(srcs.get(i), outcomes.get(i), finding -> Shrink.text(srcs.get(i), same(finding))));
  }
  List<Ast.Program> accepted(List<Ast.Program> ps){
    var srcs= ps.stream().map(Source::of).toList();
    var outcomes= srcs.parallelStream().map(this::outcome).toList();
    var res= new ArrayList<Ast.Program>();
    for (int i= 0; i < ps.size(); i += 1){
      var p= ps.get(i);
      var novelty= record(srcs.get(i), outcomes.get(i), finding -> shrink(p, finding));
      if (novelty >= 0){ res.add(p); }
      if (novelty > 0){ res.add(p); res.add(p); }
    }
    return res;
  }
  String shrink(Ast.Program p, String finding){ return Shrink.text(Source.of(Shrink.tree(p, same(finding))), same(finding)); }
  int record(String src, Outcome o, UnaryOperator<String> shrink){
    checked += 1;
    if (!o.accepted()){ rejections.merge(o.rejection(), 1, Integer::sum); }
    var worthShrinking= !o.finding().isEmpty() && (!found.containsKey(o.finding()) || found.get(o.finding()).length() > src.length());
    if (worthShrinking){ found(o.finding(), shrink.apply(o.finding())); }
    if (!o.accepted()){ return -1; }
    var ts= token.matcher(o.core()).results().map(MatchResult::group).toList();
    return (int)IntStream.range(2, ts.size()).filter(i -> triples.add(ts.get(i-2)+" "+ts.get(i-1)+" "+ts.get(i))).count();
  }
  Predicate<String> same(String finding){ return s -> outcome(s).finding().equals(finding); }
  Outcome outcome(String src){
    return outcome("p", SourceOracle.debugBuilder().put(0, src).build());
  }
  record Package(String name, SourceOracle oracle, String shown){}
  void checkPackages(List<Package> ps){
    var outcomes= ps.parallelStream().map(p -> outcome(p.name(), p.oracle())).toList();
    IntStream.range(0, ps.size()).forEach(i -> record(ps.get(i).shown(), outcomes.get(i), _ -> ps.get(i).shown()));
  }
  Outcome outcome(String pkg, SourceOracle o){
    String full;
    try{ full= full(pkg, o); }
    catch (Throwable t){ return new Outcome(crash(t), crash(t), ""); }
    var fullRejects= full.startsWith("rejects at ");
    var rejection= fullRejects ? full.substring("rejects at ".length()) : "";
    var core= fullRejects ? "" : full;
    if (!checkCompact){ return new Outcome(rejection, "", core); }
    String got;
    try{ got= compact(pkg, o); }
    catch (Throwable t){ return new Outcome(rejection, crash(t), core); }
    var compactRejects= got.startsWith("rejects at ");
    if (full.equals(got) || fullRejects && compactRejects){ return new Outcome(rejection, "", core); }
    var kind= compactRejects ? "A: the full frontend accepts, the compact frontend "+got
      : fullRejects ? "B: the compact frontend accepts, the full frontend "+full
      : "C: the full core has "+firstDifference(full, got);
    return new Outcome(rejection, kind, core);
  }
  String full(String pkg, SourceOracle o){
    try{ return canon(lines(compileAll(pkg, o, other))); }
    catch (FearlessException fe){ fe.render(o.withFallback(fallback)); return rejects(fe); }
  }
  String compact(String pkg, SourceOracle o){
    try{ return canon(compact.Print.lines(compactAll(pkg, o, compactOther))); }
    catch (compact.Frontend.Fail f){ return rejects(f); }
  }
  static final Pattern token= Pattern.compile("\\w+|\\S");
  static String firstDifference(String full, String compact){
    var f= token.matcher(full).results().map(MatchResult::group).toList();
    var c= token.matcher(compact).results().map(MatchResult::group).toList();
    var i= IntStream.range(0, Math.min(f.size(), c.size())).filter(j -> !f.get(j).equals(c.get(j))).findFirst().orElse(Math.min(f.size(), c.size()));
    return quote(f, i)+" where the compact core has "+quote(c, i);
  }
  static String quote(List<String> ts, int i){ return i < ts.size() ? "\""+ts.get(i)+"\"" : "the end"; }
  static final Pattern thrower= Pattern.compile("java\\..*|message\\.(Code|Err)\\..*|message\\.WellFormednessErrors\\.wf(Use)?|core\\.FearlessException\\..*|compact\\.Frontend(\\$Parser)?\\.(no|required|take)");
  static String rejects(Throwable t){
    var e= Stream.of(t.getStackTrace()).filter(f -> !thrower.matcher(f.getClassName()+"."+f.getMethodName()).matches()).findFirst().orElseThrow();
    return "rejects at "+e.getClassName()+"."+e.getMethodName()+":"+e.getLineNumber();
  }
  static String crash(Throwable t){
    var at= Stream.of(t.getStackTrace()).filter(e -> !e.getClassName().startsWith("java.")).findFirst();
    return t.getClass().getName()+" at "+at.map(e -> e.getClassName()+"."+e.getMethodName()).orElse("an unknown location");
  }
}
