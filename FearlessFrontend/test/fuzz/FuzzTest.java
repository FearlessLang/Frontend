package fuzz;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.StringEntry;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

import core.FearlessException;
import core.OtherPackages;
import fearlessParser.Parse;
import testUtils.DbgBlock;
import tools.SourceOracle;
import utils.Join;

public final class FuzzTest extends testUtils.FearlessTestBase{
  static final int perSeed= 9;
  static final List<String> tokens= List.of("{", "}", "(", ")", "[", "]", ":", ";", "->", "=", ",",
    "mut ", "read ", "iso ", "imm ", "readH ", "mutH ", "read/imm ", "this", " x", " .m", " .foo", "'self ",
    "::", "A", "B", "X", "_", "*", "**", "base.Void", "#", " +");
  static final Pattern undeclared= Pattern.compile("Type \"([A-Z][A-Za-z0-9_]*)\" is not declared in package");
  static final List<String> rcs= List.of("mut", "read", "imm", "iso", "readH", "mutH");
  static final Pattern rc= Pattern.compile("\\b(mut|read|imm|iso|readH|mutH)\\b");
  static final String type= "(?:(?:mut|read|imm|iso|readH|mutH) )?[A-Z][\\w.]*(?:\\[[^\\[\\]]*\\])?";
  static final List<Pattern> annotations= Stream.of(
    "\\.[a-z_]\\w*(\\[[^\\[\\]]*\\])",
    "(?<![:\\w.'])("+type+")\\{",
    "[a-z_]\\w*(:"+type+")(?=[,)])",
    "[)\\w](:"+type+")\\s*->",
    "\\b((?:mut|read|imm|iso|readH|mutH) )"
  ).map(Pattern::compile).toList();

  @Test void mutatedTestProgramsNeverCrash(){
    var seeds= seeds();
    var donors= new TreeMap<Integer,String>();
    for (var s : seeds){ donors.put(s.hashCode(), s); }
    var other= otherFrom(DbgBlock.all());
    var crashes= new TreeMap<String,String>();
    var cBase= checkCompact ? compactBase() : List.<compact.Frontend.Literal>of();
    for (var s : seeds){
      run(s, other, cBase, crashes);
      var rnd= new Random(s.hashCode());
      for (int i= 0; i < perSeed; i += 1){ run(mutate(s, rnd, donors), other, cBase, crashes); }
    }
    strCmp("", Join.of(crashes.entrySet().stream().map(e -> e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
  }
  @Test void underAnnotatedTestProgramsNeverCrash(){
    var seeds= seeds().stream().filter(FuzzTest::annotated).filter(FuzzTest::parses).toList();
    var other= otherFrom(DbgBlock.all());
    var crashes= new TreeMap<String,String>();
    var cBase= checkCompact ? compactBase() : List.<compact.Frontend.Literal>of();
    for (var s : seeds){
      var rnd= new Random(s.hashCode());
      for (int i= 0; i < perSeed; i += 1){ run(underAnnotate(s, rnd), other, cBase, crashes); }
    }
    strCmp("", Join.of(crashes.entrySet().stream().map(e -> e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
  }
  @Test void writingTheInferredTypesKeepsTheCore(){
    var other= otherFrom(DbgBlock.all());
    var cBase= checkCompact ? compactBase() : List.<compact.Frontend.Literal>of();
    var found= new TreeMap<String,String>();
    var underAnnotated= seeds().stream().filter(FuzzTest::annotated).filter(FuzzTest::parses).flatMap(FuzzTest::underAnnotations);
    Stream.concat(seeds().stream(), underAnnotated).distinct().forEach(s -> writeInferred(s, other, cBase, found));
    strCmp("", Join.of(found.entrySet().stream().map(e -> e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
  }
  static Stream<String> underAnnotations(String s){
    var rnd= new Random(s.hashCode());
    return IntStream.range(0, perSeed).mapToObj(_ -> underAnnotate(s, rnd));
  }
  static void writeInferred(String src, OtherPackages other, List<compact.Frontend.Literal> cBase, TreeMap<String,String> found){
    List<core.E.Literal> core;
    try{ core= compileAll("p", SourceOracle.debugBuilder().put(0, src).build(), other); }
    catch (Throwable _){ return; }
    var targs= new Edits(src);
    core.stream().flatMap(FuzzTest::calls).forEach(targs::call);
    var heads= new Edits(src);
    core.stream().flatMap(FuzzTest::literals).forEach(l -> heads.literal(l, false));
    var sigs= new Edits(src);
    core.stream().flatMap(FuzzTest::literals).forEach(l -> sigs.literal(l, true));
    rewrite(src, core, targs, "the inferred type arguments", other, cBase, found);
    rewrite(src, core, heads, "the inferred heads of object literals", other, cBase, found);
    rewrite(src, core, sigs, "the inferred heads and method signatures of object literals", other, cBase, found);
  }
  static void rewrite(String src, List<core.E.Literal> core, Edits edits, String what, OtherPackages other, List<compact.Frontend.Literal> cBase, TreeMap<String,String> found){
    edits.text.keySet().removeAll(edits.bad);
    var written= src;
    var got= "";
    while (true){
      if (edits.text.isEmpty()){ return; }
      written = edits.apply();
      var o= SourceOracle.debugBuilder().put(0, written).build();
      try{ got = canon(lines(compileAll("p", o, other))); }
      catch (FearlessException fe){ got = "rejected: "+fe.render(o); }
      catch (Throwable t){ got = signature(t); }
      var m= undeclared.matcher(got);
      if (!m.find()){ break; }
      var x= Pattern.compile("(^|[^A-Za-z0-9_])"+m.group(1)+"($|[^A-Za-z0-9_])");
      if (!edits.text.values().removeIf(t -> x.matcher(t).find())){ break; }
    }
    var kind= got.startsWith("rejected: ") ? "rejected after writing "+what
      : !got.contains("{") ? "crash after writing "+what+": "+got
      : got.equals(canon(lines(core))) ? "" : "different core after writing "+what;
    if (!kind.isEmpty()){ found.merge(kind, src+"\n---- written as ----\n"+written+"\n---- gives ----\n"+got+"\n---- instead of ----\n"+canon(lines(core)), FuzzTest::shorter); }
    run(written, other, cBase, found);
  }
  static Stream<core.E.Call> calls(core.E e){
    var here= e instanceof core.E.Call c ? Stream.of(c) : Stream.<core.E.Call>of();
    return Stream.concat(here, e.children().flatMap(FuzzTest::calls));
  }
  static Stream<core.E.Literal> literals(core.E e){
    var here= e instanceof core.E.Literal l ? Stream.of(l) : Stream.<core.E.Literal>of();
    return Stream.concat(here, e.children().flatMap(FuzzTest::literals));
  }
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
      for (var e : text.descendingMap().entrySet()){ res = insert(res, e.getKey(), e.getValue()); }
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
  static boolean fresh(fearlessFullGrammar.E e){ return e instanceof fearlessFullGrammar.E.Call c ? fresh(c.e()) : e instanceof fearlessFullGrammar.E.X x && x.name().startsWith("_"); }
  static void run(String src, OtherPackages other, List<compact.Frontend.Literal> cBase, TreeMap<String,String> crashes){
    var o= SourceOracle.debugBuilder().put(0, src).build();
    try{
      var expected= "error";
      try{ expected= lines(compileAll("p", o, other)); }
      catch (FearlessException fe){ fe.render(o.withFallback(DbgBlock.dbgMiniBase())); }
      if (!checkCompact){ return; }
      var got= "error";
      try{ got= compact.Print.lines(compactAll("p", o, cBase)); }
      catch (compact.Frontend.Fail _){}
      if (!canon(expected).equals(canon(got))){ crashes.merge("compact frontend disagrees", src, FuzzTest::shorter); }
    }
    catch (Throwable t){ crashes.merge(signature(t), src, FuzzTest::shorter); }
  }
  static String shorter(String a, String b){ return a.length() <= b.length() ? a : b; }
  static String signature(Throwable t){
    var at= Stream.of(t.getStackTrace()).filter(e -> !e.getClassName().startsWith("java.")).findFirst();
    return t.getClass().getName()+" at "+at.map(e -> e.getClassName()+"."+e.getMethodName()).orElse("an unknown location");
  }
  static List<String> seeds(){
    try (var files= Files.walk(testClasses())){
      return files.filter(p -> p.toString().endsWith(".class"))
        .flatMap(FuzzTest::strings).filter(FuzzTest::isProgram).distinct().sorted().toList();
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
  }
  static Path testClasses(){
    try{ return Path.of(FuzzTest.class.getProtectionDomain().getCodeSource().getLocation().toURI()); }
    catch (URISyntaxException e){ throw new IllegalStateException(e); }
  }
  static Stream<String> strings(Path classFile){
    var res= new ArrayList<String>();
    try{ for (var e : ClassFile.of().parse(classFile).constantPool()){ if (e instanceof StringEntry s){ res.add(s.stringValue()); } } }
    catch (IOException e){ throw new UncheckedIOException(e); }
    return res.stream();
  }
  static boolean isProgram(String s){
    return s.contains("\n") && !s.contains("|") && !s.contains("Error") && (s.contains("->") || s.contains(":{"));
  }
  static String mutate(String s, Random r, TreeMap<Integer,String> donors){
    int k= 1 + r.nextInt(3);
    for (int i= 0; i < k && !s.isEmpty(); i += 1){ s = mutateOnce(s, r, donors); }
    return s;
  }
  static String mutateOnce(String s, Random r, TreeMap<Integer,String> donors){
    int p= r.nextInt(s.length());
    return switch (r.nextInt(5)){
      case 0 -> s.substring(0, p) + s.substring(Math.min(s.length(), p+1+r.nextInt(4)));
      case 1 -> insert(s, p, tokens.get(r.nextInt(tokens.size())));
      case 2 -> insert(s, r.nextInt(s.length()), slice(s, p, 1+r.nextInt(12)));
      case 3 -> insert(s, p, slice(donor(donors, r), r, 20));
      default -> swapRc(s, r);
    };
  }
  static String donor(TreeMap<Integer,String> donors, Random r){
    var e= donors.ceilingEntry(r.nextInt());
    return (e == null ? donors.firstEntry() : e).getValue();
  }
  static String underAnnotate(String s, Random r){
    int k= 1 + r.nextInt(4);
    for (int i= 0; i < k; i += 1){ s = dropAnnotation(s, r); }
    return s;
  }
  static String dropAnnotation(String s, Random r){
    var byPattern= annotations.stream().map(p -> p.matcher(s).results().toList()).filter(ms -> !ms.isEmpty()).toList();
    if (byPattern.isEmpty()){ return s; }
    var ms= byPattern.get(r.nextInt(byPattern.size()));
    var m= ms.get(r.nextInt(ms.size()));
    return s.substring(0, m.start(1)) + s.substring(m.end(1));
  }
  static boolean annotated(String s){ return annotations.stream().anyMatch(p -> p.matcher(s).find()); }
  static boolean parses(String s){
    try{ Parse.from(SourceOracle.defaultDbgFearPath(0), s); return true; }
    catch (FearlessException _){ return false; }
  }
  static String insert(String s, int at, String t){ return s.substring(0, at) + t + s.substring(at); }
  static String slice(String s, int from, int maxLen){ return s.substring(from, Math.min(s.length(), from+maxLen)); }
  static String slice(String s, Random r, int maxLen){ return slice(s, r.nextInt(s.length()), 1+r.nextInt(maxLen)); }
  static String swapRc(String s, Random r){
    var ms= rc.matcher(s).results().toList();
    if (ms.isEmpty()){ return s; }
    var m= ms.get(r.nextInt(ms.size()));
    return s.substring(0, m.start()) + rcs.get(r.nextInt(rcs.size())) + s.substring(m.end());
  }
}
