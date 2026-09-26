package fuzz;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.StringEntry;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;

import core.FearlessException;
import core.OtherPackages;
import fearlessParser.Parse;
import testUtils.DbgBlock;
import tools.SourceOracle;
import utils.Join;

public class FuzzTest extends testUtils.FearlessTestBase{
  static final int Cases= 10_000;
  static final List<String> Tokens= List.of("{","}","(",")","[","]",":",";","->","=",",",
    "mut ","read ","iso ","imm ","readH ","mutH ","read/imm ","this"," x"," .m"," .foo","'self ",
    "::","A","B","X","_","*","**","base.Void","#"," +");
  static final List<String> Rcs= List.of("mut","read","imm","iso","readH","mutH");
  static final Pattern Rc= Pattern.compile("\\b(mut|read|imm|iso|readH|mutH)\\b");
  static final String Type= "(?:(?:mut|read|imm|iso|readH|mutH) )?[A-Z][\\w.]*(?:\\[[^\\[\\]]*\\])?";
  static final List<Pattern> Annotations= Stream.of(
    "\\.[a-z_]\\w*(\\[[^\\[\\]]*\\])",
    "(?<![:\\w.'])("+Type+")\\{",
    "[a-z_]\\w*(:"+Type+")(?=[,)])",
    "[)\\w](:"+Type+")\\s*->",
    "\\b((?:mut|read|imm|iso|readH|mutH) )"
  ).map(Pattern::compile).toList();

@Test void mutatedTestProgramsNeverCrash(){
  var seeds= seeds();
  var other= otherFrom(DbgBlock.all());
  var rnd= new Random(0);
  var crashes= new TreeMap<String,String>();
  for (var s : seeds){ run(s,other,crashes); }
  for (int i= 0; i < Cases; i++){ run(mutate(seeds.get(rnd.nextInt(seeds.size())),rnd,seeds),other,crashes); }
  strCmp("", Join.of(crashes.entrySet().stream().map(e->e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
}
@Test void underAnnotatedTestProgramsNeverCrash(){
  var seeds= seeds().stream().filter(FuzzTest::annotated).filter(FuzzTest::parses).toList();
  var other= otherFrom(DbgBlock.all());
  var rnd= new Random(0);
  var crashes= new TreeMap<String,String>();
  for (int i= 0; i < Cases; i++){ run(underAnnotate(seeds.get(rnd.nextInt(seeds.size())),rnd),other,crashes); }
  strCmp("", Join.of(crashes.entrySet().stream().map(e->e.getKey()+"\n"+e.getValue()), "", "\n====\n", "", ""));
}
  static void run(String src, OtherPackages other, TreeMap<String,String> crashes){
    var o= SourceOracle.debugBuilder().put(0,src).build();
    try{
      try{ compileAll("p",o,other); }
      catch(FearlessException fe){ fe.render(o.withFallback(DbgBlock.dbgMiniBase())); }
    }
    catch(Throwable t){ crashes.merge(signature(t),src,FuzzTest::shorter); }
  }
  static String shorter(String a, String b){ return a.length() <= b.length() ? a : b; }
  static String signature(Throwable t){
    var at= Stream.of(t.getStackTrace()).filter(e->!e.getClassName().startsWith("java.")).findFirst();
    return t.getClass().getName()+" at "+at.map(e->e.getClassName()+"."+e.getMethodName()).orElse("an unknown location");
  }
  static List<String> seeds(){
    try(var files= Files.walk(testClasses())){
      return files.filter(p->p.toString().endsWith(".class"))
        .flatMap(FuzzTest::strings).filter(FuzzTest::isProgram).distinct().sorted().toList();
    }
    catch(IOException e){ throw new UncheckedIOException(e); }
  }
  static Path testClasses(){
    try{ return Path.of(FuzzTest.class.getProtectionDomain().getCodeSource().getLocation().toURI()); }
    catch(URISyntaxException e){ throw new IllegalStateException(e); }
  }
  static Stream<String> strings(Path classFile){
    var res= new ArrayList<String>();
    try{ for (var e : ClassFile.of().parse(classFile).constantPool()){ if (e instanceof StringEntry s){ res.add(s.stringValue()); } } }
    catch(IOException e){ throw new UncheckedIOException(e); }
    return res.stream();
  }
  static boolean isProgram(String s){
    return s.contains("\n") && !s.contains("|") && !s.contains("Error") && (s.contains("->") || s.contains(":{"));
  }
  static String mutate(String s, Random r, List<String> seeds){
    int k= 1 + r.nextInt(3);
    for (int i= 0; i < k && !s.isEmpty(); i++){ s= mutateOnce(s,r,seeds); }
    return s;
  }
  static String mutateOnce(String s, Random r, List<String> seeds){
    int p= r.nextInt(s.length());
    return switch (r.nextInt(5)){
      case 0 -> s.substring(0,p) + s.substring(Math.min(s.length(),p+1+r.nextInt(4)));
      case 1 -> insert(s,p,Tokens.get(r.nextInt(Tokens.size())));
      case 2 -> insert(s,r.nextInt(s.length()),slice(s,p,1+r.nextInt(12)));
      case 3 -> insert(s,p,slice(seeds.get(r.nextInt(seeds.size())),r,20));
      default -> swapRc(s,r);
    };
  }
  static String underAnnotate(String s, Random r){
    int k= 1 + r.nextInt(4);
    for (int i= 0; i < k; i++){ s= dropAnnotation(s,r); }
    return s;
  }
  static String dropAnnotation(String s, Random r){
    var byPattern= Annotations.stream().map(p->p.matcher(s).results().toList()).filter(ms->!ms.isEmpty()).toList();
    if (byPattern.isEmpty()){ return s; }
    var ms= byPattern.get(r.nextInt(byPattern.size()));
    var m= ms.get(r.nextInt(ms.size()));
    return s.substring(0,m.start(1)) + s.substring(m.end(1));
  }
  static boolean annotated(String s){ return Annotations.stream().anyMatch(p->p.matcher(s).find()); }
  static boolean parses(String s){
    try{ Parse.from(SourceOracle.defaultDbgFearPath(0), s); return true; }
    catch(FearlessException _){ return false; }
  }
  static String insert(String s, int at, String t){ return s.substring(0,at) + t + s.substring(at); }
  static String slice(String s, int from, int maxLen){ return s.substring(from,Math.min(s.length(),from+maxLen)); }
  static String slice(String s, Random r, int maxLen){ return slice(s,r.nextInt(s.length()),1+r.nextInt(maxLen)); }
  static String swapRc(String s, Random r){
    List<MatchResult> ms= Rc.matcher(s).results().toList();
    if (ms.isEmpty()){ return s; }
    var m= ms.get(r.nextInt(ms.size()));
    return s.substring(0,m.start()) + Rcs.get(r.nextInt(Rcs.size())) + s.substring(m.end());
  }
}
