package testUtils;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import org.junit.jupiter.api.Assertions;
import org.opentest4j.AssertionFailedError;

import compact.Frontend;
import compact.Print;
import compact.Frontend.Fail;
import core.OtherPackages;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.ToString;
import fearlessParser.Parse;
import inject.Methods;
import core.FearlessException;
import main.FrontendLogicMain;
import main.InferenceMain;
import tools.SourceOracle;
import utils.Err;
import utils.Join;
import utils.Pos;
import utils.Range;

public abstract class FearlessTestBase{

  static{ Err.setUp(AssertionFailedError.class, Assertions::assertEquals, Assertions::assertTrue); }
  protected static final boolean checkCompact= Boolean.getBoolean("compact");

  protected static String stripWs(String s){ return s.replace("\n", "").replace(" ", ""); }
  protected static void strCmp(String expected, String got){ Err.strCmp(expected, got); }

  protected static SourceOracle oraclePkg(List<String> bodies){
    var b= SourceOracle.debugBuilder();
    for (int i : Range.of(bodies)){ b = b.put(i, bodies.get(i)); }
    return b.build();
  }
  protected static <R> R printError(Supplier<R> r, SourceOracle o){
    try{ return r.get(); }
    catch (FearlessException fe){
      o = o.withFallback(DbgBlock.dbgMiniBase());
      System.out.println(fe.render(o));
      throw fe;
    }
  }
  protected static void parseOkNormalized(String expectedNoWs, String input){
    var res= Parse.from(Pos.unknown.fileName(), input);
    strCmp(stripWs(expectedNoWs), stripWs(res.toString()));
  }
  protected static void parseFail(String expectedErr, String input){
    var o= oraclePkg(List.of(input));
    var fe= assertThrows(FearlessException.class,
      () -> Parse.from(SourceOracle.defaultDbgFearPath(0), input));
    strCmp(expectedErr, fe.render(o));
  }
  protected static Methods parsePackage(String pkgName, SourceOracle o, OtherPackages other, boolean infer){
    return new InferenceMain().ofMethods(pkgName, o.allFiles(), o, other, infer);
  }
  protected static Methods parsePackage(String pkgName, SourceOracle o, boolean infer){
    return parsePackage(pkgName, o, otherFrom(DbgBlock.all()), infer);
  }
  protected static void toStringOk(String expected, String input){
    FileFull res;
    try{ res= Parse.from(SourceOracle.defaultDbgFearPath(0), input); }
    catch (FearlessException fe){
      var o= SourceOracle.debugBuilder().put(0, input).build();
      System.out.println(fe.render(o));
      throw fe;
    }
    var got= Join.of(
      res.decs().stream().map(ToString::declaration),
      "",
      "\n",
      "\n",
      ""
    );
    Err.strCmp(expected, got);
  }
  protected static void inferenceOk(String expected, List<String> input, boolean infer){
    var o= oraclePkg(input);
    var res= printError(() -> parsePackage("p", o, infer), o);
    var got= Join.of(res.p().log().logs().stream().sorted(), "", "\n", "", "");
    strCmp(expected, got);
  }
  protected static void inferenceFail(String expected, List<String> input, boolean infer){
    var o= oraclePkg(input);
    var fe= assertThrows(FearlessException.class, () -> parsePackage("p", o, infer));
    strCmp(expected, fe.render(o));
  }
  protected static void inferenceFail(String expected, List<String> input){
    inferenceFail(expected, input, false);
  }
  protected static void typeOk(List<String> input){
    var o= oraclePkg(input);
    var base= printError(DbgBlock::all, o);
    var res= printError(() -> new FrontendLogicMain().of("p", Map.of(), o.allFiles(), otherFrom(base)), o);
    if (!checkCompact){ return; }
    var compactBase= compactBase();
    strCmp(lines(base), Print.lines(compactBase));
    strCmp(lines(res), Print.lines(compactAll("p", o, compactBase)));
  }
  protected static void typeFailRaw(String expected, List<String> input){
    var o= oraclePkg(input);
    var other= otherFrom(DbgBlock.all());
    var fe= assertThrows(FearlessException.class,
      () -> new FrontendLogicMain().of("p", Map.of(), o.allFiles(), other));
    strCmp(expected, fe.render(o));
    if (!checkCompact){ return; }
    var compactBase= compactBase();
    assertThrows(Fail.class, () -> compactAll("p", o, compactBase));
  }
  protected static String lines(List<?> res){ return Join.of(res, "", "\n", "", ""); }
  protected static List<Frontend.Literal> compactBase(){
    return compactAll("base", DbgBlock.dbgMiniBase(), List.of());
  }
  protected static List<Frontend.Literal> compactAll(String pkgName, SourceOracle o, List<Frontend.Literal> other){
    var files= new LinkedHashMap<String,String>();
    for (var r : o.allFiles()){ files.put(r.fearPath(), r.loadString()); }
    return Frontend.compile(pkgName, Map.of(), files, other);
  }
  protected static void typeFail(String expected, List<String> input){
    typeFailRaw("In file: [###].fear\n\n"+expected+"Error 8 TypeError", input);
  }
  protected static OtherPackages otherErr(){ return OtherPackages.empty(); }

  protected static OtherPackages otherFrom(List<core.E.Literal> ds){ return OtherPackages.start(Map.of(), ds, -1); }
  protected static List<core.E.Literal> compileAll(String pkgName, SourceOracle o, OtherPackages other){
    return new FrontendLogicMain().of(pkgName, Map.of(), o.allFiles(), other);
  }
  protected static <T> T okOrPrint(SourceOracle o, Supplier<T> run){
    try{ return run.get(); }
    catch (FearlessException fe){
      System.out.println(fe.render(o));
      throw fe;
    }
  }
  protected static void okOrPrint(SourceOracle o, Runnable run){
    okOrPrint(o, () -> { run.run(); return null; });
  }
}