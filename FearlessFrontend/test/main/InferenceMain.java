package main;

import java.util.List;
import java.util.Map;

import core.OtherPackages;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import inference.E;
import inject.InjectionSteps;
import inject.Methods;
import inject.ToInference;
import pkgmerge.DeclaredNames;
import pkgmerge.Package;
import tools.SourceOracle;
import tools.SourceOracle.Ref;

public class InferenceMain extends FrontendLogicMain{
  @Override Package makePackage(String name, Map<String,String> map, List<Declaration> decs, DeclaredNames names){
    return new Package(name, map, decs, names, Package.onLogger());
  }
  public Methods ofMethods(String pkgName, List<Ref> files, SourceOracle o, OtherPackages other, boolean infer){
    Map<Ref, FileFull> rawAST= parseFiles(files, o);
    Package pkg= mergeToPackage(pkgName,rawAST, Map.of(), other);
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
