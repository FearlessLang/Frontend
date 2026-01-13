package main;

import static offensiveUtils.Require.*;
import static fearlessParser.TokenKind.*;
import java.net.URI;
import java.util.*;

import pkgmerge.DeclaredNames;
import pkgmerge.Package;
import core.OtherPackages;
import core.TName;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import fearlessParser.Parse;
import inject.InjectionSteps;
import inject.Methods;
import inject.ToInference;
import message.WellFormednessErrors;
import tools.SourceOracle;
import typeSystem.TypeSystem;

public class FrontendLogicMain {
  public List<core.E.Literal> of(
      String pkgName,
      Map<String,String> override, 
      List<URI> files, 
      SourceOracle o, 
      OtherPackages other
    ){
    Map<URI, FileFull> rawAST= parseFiles(files, o); // Phase 1: Parse Files
    Package pkg= mergeToPackage(pkgName,rawAST, override, other); // Phase 2: Merge & Well-formedness
    Methods ctx= Methods.create(pkg, other); // Phase 3: // Creates the scope (Methods) and FreshPrefix generators
    List<inference.E.Literal> inferrableAST= new ToInference().of(pkg, ctx, other, ctx.fresh()); // Phase 4: Desugar
    inferrableAST = ctx.registerTypeHeadersAndReturnRoots(inferrableAST); // Phase 5: Build Synthetic type table inside ctx
    List<core.E.Literal> coreAST = InjectionSteps.steps(ctx, inferrableAST);  // Phase 6: Inference
    TypeSystem.allOk(coreAST, pkg, other); //Phase 7: type checking
    return coreAST;
  }
  protected Map<URI, FileFull> parseFiles(List<URI> files, SourceOracle o){
    Map<URI, FileFull> all = new LinkedHashMap<>();
    for (var u : files) {
      var str = o.loadString(u);
      all.put(u, Parse.from(u, str));
    }
    return all;
  }  
  private void checkOnlyHeadHasDirectives(WellFormednessErrors err, URI headPkg, Map<URI, FileFull> raw){
    raw.entrySet().stream()
      .filter(e -> !e.getKey().equals(headPkg))
      .filter(e -> !e.getValue().noDirectives())
      .forEach(e -> { throw err.notClean(e.getKey(), e.getValue()); });  
  }
  protected Package mergeToPackage(String pkgName,Map<URI, FileFull> raw, Map<String,String> override, OtherPackages other){
    assert !raw.isEmpty();
    var err= new WellFormednessErrors(pkgName);
    URI headPkg= findHeadUri(err,pkgName, raw.keySet());
    checkOnlyHeadHasDirectives(err,headPkg, raw);
    var head= raw.get(headPkg);
    var map= new HashMap<String, String>(override);
    accUses(err,pkgName, map, head.uses(), other);
    List<Declaration> ds= raw.values().stream().flatMap(f -> f.decs().stream()).toList();
    var names= DeclaredNames.of(pkgName, ds, Collections.unmodifiableMap(map));    
    return makePackage(pkgName, map, ds, names);
  }
  protected Package makePackage(String name, Map<String,String> map, List<Declaration> decs, DeclaredNames names){
    return new Package(name,map,decs,names,Package.offLogger());//this method exists to change logger in mocking
  }
  //map a as b in c //inside c, replace b with a
  private void accUses(WellFormednessErrors err, String n, HashMap<String, String> map, List<FileFull.Use> uses, OtherPackages other) {
    Collection<TName> otherDom= uses.isEmpty() ? List.of() : other.dom();
    for (var u : uses) {
      var p= u.in().pkgName();
      p = map.getOrDefault(p, p); //thus if p is "" we get ""
      map.put(u.out(), p + "." + u.in().simpleName());
      var ok= otherDom.stream().anyMatch(e -> e.s().equals(u.in().s()));
      if (!ok){ throw err.unknownUseHead(u.in()); }
    }//map a as b in c + use b.F as bF will replace bF with a.F
  }
  private URI findHeadUri(WellFormednessErrors err, String pkgName, Set<URI> uris){
    assert nonNull(uris) && validate(pkgName,"",_pkgName);
    var heads= uris.stream().filter(u->isHeadUri(u)).toList();
    if (heads.size() == 1){ return heads.getFirst(); }
    throw err.expectedSingleUriForPackage(heads,pkgName);
  }
  private boolean isHeadUri(URI u){
    String name= fileName(u);
    int dot= name.lastIndexOf('.');
    return dot > 0 && name.substring(0,dot).startsWith("_rank_");
  }
  private String fileName(URI u){
    String p= u.getPath();
    int slash= p.lastIndexOf('/');//Ok, portable because u is URI
    return slash >= 0 ? p.substring(slash + 1) : p;
  }
}