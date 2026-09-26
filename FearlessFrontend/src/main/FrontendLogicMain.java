package main;

import static offensiveUtils.Require.*;
import static fearlessParser.TokenKind.*;

import java.util.*;
import java.util.stream.Collectors;

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
import metaParser.PrettyFileName;
import tools.Fs;
import tools.SourceOracle;
import tools.SourceOracle.Ref;
import typeSystem.TypeSystem;

public class FrontendLogicMain{
  public List<core.E.Literal> of(
      String pkgName,
      Map<String,String> override,
      List<Ref> files, 
      SourceOracle o, 
      OtherPackages other
    ){
    Map<Ref, FileFull> rawAST= parseFiles(files); // Phase 1: Parse Files
    Package pkg= mergeToPackage(pkgName,rawAST, override, other); // Phase 2: Merge & Well-formedness
    Methods ctx= Methods.create(pkg, other); // Phase 3: // Creates the scope (Methods) and FreshPrefix generators
    List<inference.E.Literal> inferrableAST= new ToInference().of(ctx); // Phase 4: Desugar
    inferrableAST= ctx.registerTypeHeadersAndReturnRoots(inferrableAST); // Phase 5: Build Synthetic type table inside ctx
    List<core.E.Literal> coreAST= InjectionSteps.steps(ctx, inferrableAST);  // Phase 6: Inference
    TypeSystem.allOk(coreAST, pkg, other); //Phase 7: type checking
    return coreAST;
  }
  public Map<String,Map<String,String>> parseRankFiles(List<Ref> files, SourceOracle o, Comparator<Ref> c){
    var parsed= parseFiles(files);
    record Key(String target,String in){}
    record Cand(Ref uri,String target,String in,String out){
    @Override public String toString(){
      String f= PrettyFileName.displayFileName(uri.fearURI());
      return " - "+f+"\n"
           + "   \"map  "+in+"  as  "+out+"  in  "+target+";\"";
    }}
    Map<Key,List<Cand>> byKey= parsed.entrySet().stream()
      .flatMap(e->e.getValue().maps().stream().map(m->new Cand(e.getKey(), m.target(), m.in(), m.out())
      )).collect(Collectors.groupingBy(x->new Key(x.target(),x.in())));
    Map<String,Map<String,String>> res= new HashMap<>();
    for (var e : byKey.entrySet()){
      var k= e.getKey();
      var cs= e.getValue();
      var best= cs.stream().max(Comparator.comparing(Cand::uri,c)).get();
      List<Cand> bests= cs.stream().filter(x->c.compare(x.uri(), best.uri())==0).toList();
      // What to do if two different rank files with the SAME RANK give the SAME MAPPING? Here we are tolerant.
      var conflicting= bests.stream().map(Cand::out).distinct().count() != 1;
      if (conflicting){ throw new WellFormednessErrors(k.target()).mapConflict(k.in(), bests.stream().map(Object::toString).toList()); }
      res.computeIfAbsent(k.target(), _->new HashMap<>()).put(k.in(), best.out());
    }
    res.replaceAll((_,v)->Map.copyOf(v));
    return Map.copyOf(res);
  }
  Map<Ref, FileFull> parseFiles(List<Ref> files){
    Map<Ref, FileFull> all= new LinkedHashMap<>();
    for (var u : files){ all.put(u, Parse.from(u.fearURI(), u.loadString())); }
    return Collections.unmodifiableMap(all);
  }
  private void checkOnlyHeadHasDirectives(WellFormednessErrors err, Ref headPkg, Map<Ref, FileFull> raw){
    raw.entrySet().stream()
      .filter(e->!e.getKey().equals(headPkg))
      .filter(e->!e.getValue().noDirectives())
      .forEach(e->{ throw err.notClean(e.getKey(), e.getValue()); });  
  }
  Package mergeToPackage(String pkgName,Map<Ref, FileFull> raw, Map<String,String> override, OtherPackages other){
    assert !raw.isEmpty();
    var err= new WellFormednessErrors(pkgName);
    Ref headPkg= findHeadUri(err, raw.keySet());
    checkOnlyHeadHasDirectives(err,headPkg, raw);
    var head= raw.get(headPkg);
    var map= new HashMap<String, String>(override);
    accUses(err, map, head.uses(), other);
    List<Declaration> ds= raw.values().stream()
      .flatMap(f->f.decs().stream())
      .sorted().toList();
    Map<String,String> readOnlyMap= Collections.unmodifiableMap(map);
    var names= DeclaredNames.of(pkgName, ds, readOnlyMap);
    return makePackage(pkgName, readOnlyMap, ds, names);
  }
  Package makePackage(String name, Map<String,String> map, List<Declaration> decs, DeclaredNames names){
    return new Package(name,map,decs,names,Package.offLogger());//this method exists to change logger in mocking
  }
  //map a as b in c //inside c, a written a stands for b
  private void accUses(WellFormednessErrors err, HashMap<String, String> map, List<FileFull.Use> uses, OtherPackages other){
    Collection<TName> otherDom= uses.isEmpty() ? List.of() : other.dom();
    for (var u : uses){
      var p= u.in().pkgName();
      p= map.getOrDefault(p, p); //thus if p is "" we get ""
      var in= p + "." + u.in().simpleName();
      map.put(u.out(), in);
      var ok= otherDom.stream().anyMatch(e->e.s().equals(in));
      if (!ok){ throw err.unknownUseHead(u.in(), p); }
    }//map a as b in c + use a.F as aF will replace aF with b.F
  }
  private Ref findHeadUri(WellFormednessErrors err, Set<Ref> uris){
    assert nonNull(uris);
    assert validate(err.pkgName(),"",_pkgName);
    var heads= uris.stream().filter(this::isHeadUri).toList();
    if (heads.size() == 1){ return heads.getFirst(); }
    throw err.expectedSingleUriForPackage(heads);
  }
  private boolean isHeadUri(Ref u){
    String name= Fs.fileNameWithExtension(u.fearPath());
    int dot= name.lastIndexOf('.');
    return dot > 0 && name.substring(0,dot).startsWith("_rank_");
  }
}