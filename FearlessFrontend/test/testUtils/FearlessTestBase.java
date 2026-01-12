package testUtils;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Assertions;
import org.opentest4j.AssertionFailedError;

import core.OtherPackages;
import core.TName;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.FileFull.Role;
import fearlessFullGrammar.ToString;
import fearlessParser.Parse;
import inference.E;
import inject.InjectionSteps;
import inject.Methods;
import inject.ToInference;
import message.FearlessException;
import pkgmerge.DeclaredNames;
import main.FrontendLogicMain;
import pkgmerge.Package;
import tools.SourceOracle;
import utils.Bug;
import utils.Err;
import utils.Join;
import utils.Pos;

public abstract class FearlessTestBase{
  protected static final String defaultPkg="p";
  protected static final String defaultHead="role app000;";

  static{ Err.setUp(AssertionFailedError.class, Assertions::assertEquals, Assertions::assertTrue); }

  protected static String stripWs(String s){ return s.replace("\n","").replace(" ",""); }
  protected static void strCmp(String expected, String got){ Err.strCmp(expected, got); }

  protected static SourceOracle oracleRaw(List<String> files){
    var b= SourceOracle.debugBuilder();
    for (int i= 0; i < files.size(); i += 1){ b= b.put(i, files.get(i)); }
    return b.build();
  }
  protected static SourceOracle oraclePkg(String pkgName, String head, List<String> bodies){
    var b= SourceOracle.debugBuilder();
    b.put(pkgName+".fear", "package "+pkgName+";\n"+head);
    for (int i= 0; i < bodies.size(); i += 1){
      b= b.put(i, "package "+pkgName+";\n"+bodies.get(i));
    }
    return b.build();
  }
  protected static SourceOracle oraclePkg(String head, List<String> bodies){
    return oraclePkg(defaultPkg, head, bodies);
  }
  protected static SourceOracle oraclePkg(List<String> bodies){
    return oraclePkg(defaultPkg, defaultHead, bodies);
  }
  protected static List<URI> filesUri(int n){
    return IntStream.range(0, n).mapToObj(SourceOracle::defaultDbgUri).toList();
  }
  protected static <R> R printError(Supplier<R> r, SourceOracle o){
    try{ return r.get(); }
    catch(FearlessException fe){
      o=o.withFallback(DbgBlock.dbgMiniBase()); 
      System.out.println(fe.render(o));
      throw fe;
    }
  }
  protected static FileFull parseFull(String input){
    return printError(() -> Parse.from(SourceOracle.defaultDbgUri(0), input), oracleRaw(List.of(input)));
  }
  protected static void parseOkNormalized(String expectedNoWs, String input){
    FileFull res= Parse.from(Pos.unknown.fileName(), input);
    strCmp(stripWs(expectedNoWs), stripWs(res.toString()));
  }
  protected static void parseFail(String expectedErr, String input){
    SourceOracle o= oracleRaw(List.of(input));
    FearlessException fe= assertThrows(FearlessException.class,
      () -> Parse.from(SourceOracle.defaultDbgUri(0), input));
    strCmp(expectedErr, fe.render(o));
  }
  protected static Methods parsePackage(SourceOracle o, OtherPackages other, boolean infer){
    class InferenceMain extends FrontendLogicMain{
      @Override protected Package makePackage(String name, Role role, Map<String,String> map, List<Declaration> decs, DeclaredNames names){
        return new Package(name, role, map, decs, names, Package.onLogger());
      }
      Methods ofMethods(List<FileFull.Map> override, List<URI> files, SourceOracle o, OtherPackages other, boolean infer){
        Map<URI, FileFull> rawAST= parseFiles(files, o);
        Package pkg= mergeToPackage(rawAST, override, other);
        Methods ctx= Methods.create(pkg, other);
        List<E.Literal> iDecs= new ToInference().of(ctx.p(), ctx, other, ctx.fresh());
        iDecs= ctx.registerTypeHeadersAndReturnRoots(iDecs);
        if (!infer){ return ctx; }
        var res= InjectionSteps.steps(ctx, iDecs);
        ctx.p().log().logs().add("~-----------");
        for (var r: res){ ctx.p().log().logs().add("~"+r); }
        return ctx;
      }
    }
    return new InferenceMain().ofMethods(List.of(), o.allFiles(), o, other, infer);
  }
  protected static Methods parsePackage(SourceOracle o, boolean infer){
    return parsePackage(o, otherFrom(DbgBlock.all()), infer);
  }
  protected static void toStringOk(String expected,String input){
    FileFull res;
    try{ res= Parse.from(SourceOracle.defaultDbgUri(0), input); }
    catch(FearlessException fe){
      SourceOracle o= SourceOracle.debugBuilder().put(0, input).build();
      System.out.println(fe.render(o));
      throw fe;
    }
    String got= Join.of(
      res.decs().stream().map(ToString::declaration),
      "",
      "\n",
      "\n",
      ""
    );
    Err.strCmp(expected,got);
  }
  protected static void inferenceOk(String expected, String head, List<String> input, boolean infer){
    var o= oraclePkg(defaultPkg, head, input);
    Methods res= printError(() -> parsePackage(o, infer), o);
    String got= Join.of(res.p().log().logs().stream().sorted(), "", "\n", "", "");
    strCmp(expected, got);
  }
  protected static void inferenceOk(String expected, String head, List<String> input){ inferenceOk(expected, head, input, false); }
  protected static void inferenceOk(String expected, List<String> input){ inferenceOk(expected, defaultHead, input, false); }
  protected static void inferenceFail(String expected, String head, List<String> input, boolean infer){
    var o= oraclePkg(defaultPkg, head, input);
    FearlessException fe= assertThrows(FearlessException.class, () -> parsePackage(o, infer));
    strCmp(expected, fe.render(o));
  }
  protected static void inferenceFail(String expected, String head, List<String> input){
    inferenceFail(expected, head, input, false);
  }
  protected static void inferenceFailI(String expected, String head, List<String> input){
    inferenceFail(expected, head, input, true);
  }
  protected static void inferenceFail(String expected, List<String> input){
    inferenceFail(expected, defaultHead, input, false);
  }
  protected static void typeOk(String head, List<String> input){
    var o= oraclePkg(defaultPkg, head, input);
    OtherPackages other=  printError(() -> otherFrom(DbgBlock.all()),o);
    printError(() -> new FrontendLogicMain().of(List.of(), o.allFiles(), o, other), o);
  }
  protected static void typeOk(List<String> input){ typeOk(defaultHead, input); }

  protected static void typeFail(String expected, String head, List<String> input){
    var o= oraclePkg(defaultPkg, head, input);
    OtherPackages other= otherFrom(DbgBlock.all());
    FearlessException fe= assertThrows(FearlessException.class,
      () -> new FrontendLogicMain().of(List.of(), o.allFiles(), o, other));
    strCmp(expected, fe.render(o));
  }
  protected static void typeFailExt(String expected, List<String> input){ typeFail(expected, defaultHead, input); }
  protected static void typeFail(String expected, List<String> input){
    typeFail("In file: [###]/in_memory0.fear\n\n"+expected+"Error 10 TypeError", defaultHead, input);
  }
  protected static OtherPackages otherErr(){ return OtherPackages.empty(); }

  protected static OtherPackages otherFrom(List<core.E.Literal> ds){
    var map= ds.stream().collect(Collectors.toMap(core.E.Literal::name, d->d));
    return new OtherPackages(){
      public core.E.Literal of(TName name){ return map.get(name); } // null on miss on purpose: this is to allow adding type literals on top
      public Collection<TName> dom(){ return map.keySet(); }
    };
  }
  protected static List<core.E.Literal> compileAll(SourceOracle o, OtherPackages other){
    return new main.FrontendLogicMain().of(List.of(), o.allFiles(), o, other);
  }
  protected static List<core.E.Literal> compileAllOk(SourceOracle o, core.OtherPackages other){
    return okOrPrint(o, ()->compileAll(o, other));
  }
  public static SourceOracle oracleFromDir(Path root){
    if (!Files.isDirectory(root)){ throw Bug.of("Not a directory: "+root); }
    var b= SourceOracle.debugBuilder();
    try{
      var files= Files.walk(root)
        .filter(p->Files.isRegularFile(p) && p.toString().endsWith(".fear"))
        .sorted(Comparator.comparing(p->root.relativize(p).toString()))
        .toList();
      if (files.isEmpty()){ throw Bug.of("No .fear files under: "+root); }
      for (var p:files){
        String src= Files.readString(p);
        URI u= p.toAbsolutePath().normalize().toUri();
        b = b.putURI(u, src);
      }
      return b.build();
    }
    catch(IOException e){ throw new UncheckedIOException(e); }
  }
  protected static <T> T okOrPrint(SourceOracle o, Supplier<T> run){
    try{ return run.get(); }
    catch(FearlessException fe){
      System.out.println(fe.render(o));
      throw fe;
    }
  }
  protected static void okOrPrint(SourceOracle o, Runnable run){
    okOrPrint(o, ()->{ run.run(); return null; });
  }
}