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
import tools.SourceOracle.Ref;
import typeSystem.TypeSystem;

public class FrontendLogicMain{
  public List<core.E.Literal> of(
      String pkgName,
      Map<String,String> override,
      List<Ref> files,
      OtherPackages other
    ){
    var rawAST= parseFiles(files); // Phase 1: Parse Files
    var pkg= mergeToPackage(pkgName,rawAST, override, other); // Phase 2: Merge & Well-formedness
    var ctx= Methods.create(pkg, other); // Phase 3: // Creates the scope (Methods) and FreshPrefix generators
    var inferrableAST= ToInference.of(ctx); // Phase 4: Desugar
    inferrableAST= ctx.registerTypeHeadersAndReturnRoots(inferrableAST); // Phase 5: Build Synthetic type table inside ctx
    var coreAST= InjectionSteps.steps(ctx, inferrableAST);  // Phase 6: Inference
    TypeSystem.allOk(coreAST, pkg, other); //Phase 7: type checking
    return coreAST;
  }
  public Map<String,Map<String,String>> parseRankFiles(List<Ref> files, Comparator<Ref> c, Collection<String> pkgs){
    var parsed= parseFiles(files);
    record Key(String target,String in){}
    record Cand(Ref uri,String target,String in,String out){
    public String toString(){
      var f= PrettyFileName.displayFileName(uri.fearURI());
      return " - "+f+"\n"
           + "   \"map  "+in+"  as  "+out+"  in  "+target+";\"";
    }}
    var byKey= parsed.entrySet().stream()
      .flatMap(e->e.getValue().maps().stream().map(m->new Cand(e.getKey(), m.target(), m.in(), m.out())
      )).collect(Collectors.groupingBy(x->new Key(x.target(),x.in())));
    var res= new HashMap<String,HashMap<String,String>>();
    for (var e : byKey.entrySet()){
      var k= e.getKey();
      var cs= e.getValue();
      var best= cs.stream().max(Comparator.comparing(Cand::uri,c)).get();
      var bests= cs.stream().filter(x->c.compare(x.uri(), best.uri()) == 0).toList();
      // What to do if two different rank files with the SAME RANK give the SAME MAPPING? Here we are tolerant.
      var conflicting= bests.stream().map(Cand::out).distinct().count() != 1;
      if (conflicting){ throw new WellFormednessErrors(k.target()).mapConflict(k.in(), bests.stream().map(Object::toString).toList()); }
      if (!pkgs.contains(best.out())){ throw new WellFormednessErrors(k.target()).mapToMissingPackage(k.in(), best.out(), best.toString(), pkgs.stream().sorted().toList()); }
      res.computeIfAbsent(k.target(), _->new HashMap<>()).put(k.in(), best.out());
    }
    return res.entrySet().stream().collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, e->Map.copyOf(e.getValue())));
  }
  Map<Ref,FileFull> parseFiles(List<Ref> files){
    var all= new LinkedHashMap<Ref,FileFull>();
    for (var u : files){ all.put(u, Parse.from(u.fearURI(), u.loadString())); }
    return Collections.unmodifiableMap(all);
  }
  Package mergeToPackage(String pkgName,Map<Ref,FileFull> raw, Map<String,String> override, OtherPackages other){
    assert !raw.isEmpty();
    var err= new WellFormednessErrors(pkgName);
    var headPkg= findHeadUri(err, raw.keySet());
    raw.entrySet().stream()
      .filter(e->!e.getKey().equals(headPkg) && !e.getValue().noDirectives())
      .forEach(e->{ throw err.notClean(e.getKey(), e.getValue()); });
    var head= raw.get(headPkg);
    var ds= raw.values().stream()
      .flatMap(f->f.decs().stream())
      .sorted().toList();
    var names= DeclaredNames.of(pkgName, ds, head.uses().stream().map(FileFull.Use::out).collect(Collectors.toUnmodifiableSet()));
    var map= new HashMap<String,String>(override);
    accUses(err, map, head.uses(), other, names);
    return makePackage(pkgName, Collections.unmodifiableMap(map), head.uses(), ds, names);
  }
  Package makePackage(String name, Map<String,String> map, List<FileFull.Use> uses, List<Declaration> decs, DeclaredNames names){
    return new Package(name,map,uses,decs,names,new Package.Logger(false,null));//this method exists to change logger in mocking
  }
  //map a as b in c //inside c, a written a stands for b
  private void accUses(WellFormednessErrors err, HashMap<String,String> map, List<FileFull.Use> uses, OtherPackages other, DeclaredNames names){
    Collection<TName> otherDom= uses.isEmpty() ? List.of() : other.dom();
    for (var u : uses){
      var p= u.in().pkgName();
      p= map.getOrDefault(p, p); //thus if p is "" we get ""
      var in= p + "." + u.in().simpleName();
      map.put(u.out(), in);
      var dom= p.equals(err.pkgName()) ? names.decNames().stream().map(n->n.withPkgName(err.pkgName())) : otherDom.stream();
      var ok= dom.anyMatch(e->e.s().equals(in));
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
    var name= Fs.fileNameWithExtension(u.fearPath());
    var dot= name.lastIndexOf('.');
    return dot > 0 && name.substring(0,dot).startsWith("_rank_");
  }
}