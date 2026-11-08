package fuzz;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;
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
  final OtherPackages other= otherFrom(DbgBlock.all());
  final List<compact.Frontend.Literal> compactOther= checkCompact ? compactBase() : List.of();
  final String name;
  final TreeMap<String,String> found= new TreeMap<>();
  final TreeMap<String,Integer> rejections= new TreeMap<>();
  int checked= 0;
  Fuzz(String name){ this.name= name; }
  void found(String key, String program){ found.merge(key, program, (a, b) -> a.length() <= b.length() ? a : b); }
  void assertNothingFound(){
    System.out.println(summary());
    strCmp("", Join.of(found.entrySet().stream().map(e -> e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
  }
  String summary(){
    var rejected= rejections.values().stream().mapToInt(i -> i).sum();
    var frequent= rejections.entrySet().stream().sorted(Map.Entry.<String,Integer>comparingByValue().reversed()).limit(3).map(e -> e.getKey()+" "+e.getValue());
    return name+": "+checked+" programs, "+(checked-rejected)+" accepted by the full frontend; most frequent rejections: "+Join.of(frequent, "", ", ", "", "");
  }
  void check(String src){
    var o= SourceOracle.debugBuilder().put(0, src).build();
    checked += 1;
    try{
      String full;
      try{ full= canon(lines(compileAll("p", o, other))); }
      catch (FearlessException fe){ fe.render(o.withFallback(DbgBlock.dbgMiniBase())); full= rejects(fe); rejections.merge(full.substring("rejects at ".length()), 1, Integer::sum); }
      if (!checkCompact){ return; }
      String got;
      try{ got= canon(compact.Print.lines(compactAll("p", o, compactOther))); }
      catch (compact.Frontend.Fail f){ got= rejects(f); }
      var fullRejects= full.startsWith("rejects at ");
      var compactRejects= got.startsWith("rejects at ");
      if (full.equals(got) || fullRejects && compactRejects){ return; }
      var kind= compactRejects ? "A: the full frontend accepts, the compact frontend "+got
        : fullRejects ? "B: the compact frontend accepts, the full frontend "+full
        : "C: the full core has "+firstDifference(full, got);
      found(kind, src);
    }
    catch (Throwable t){ found(crash(t), src); }
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
