package main;

import static offensiveUtils.Require.*;
import static fearlessParser.TokenKind.*;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import pkgmerge.DeclaredNames;
import pkgmerge.Package;
import core.AllLs;
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
import utils.Push;

public class FrontendLogicMain{
  public List<core.E.Literal> of(
      String pkgName,
      Map<String,String> override,
      List<Ref> files,
      OtherPackages other
    ){
    return of(pkgName, override, files, other, _ -> Optional.empty());
  }
  public List<core.E.Literal> of(
      String pkgName,
      Map<String,String> override,
      List<Ref> files,
      OtherPackages other,
      Function<List<core.E.Literal>,Optional<Ref>> tests
    ){
    var rawAST= parseFiles(files); // Phase 1: Parse Files
    var pkg= mergeToPackage(pkgName, rawAST, override, other); // Phase 2: Merge & Well-formedness
    var ctx= Methods.create(pkg, other); // Phase 3: // Creates the scope (Methods) and FreshPrefix generators
    var coreAST= core(ctx);
    var test= tests.apply(coreAST);
    if (test.isEmpty()){ return coreAST; }
    var testAST= Parse.from(test.get().fearURI(), test.get().loadString());
    var raw= new LinkedHashMap<>(rawAST);
    raw.put(test.get(), testAST);
    var all= mergeToPackage(pkgName, raw, override, other);
    var testPkg= makePackage(pkgName, all.map(), all.uses(), testAST.decs().stream().sorted().toList(), all.names());
    var lits= AllLs.of(coreAST);
    var testCtx= Methods.create(testPkg, other.mergeWith(lits, other.stamp()));
    lits.keySet().forEach(n -> testCtx.fresh().usedTopTypes().add(n.simpleName()));
    return Push.of(coreAST, core(testCtx));
  }
  private static List<core.E.Literal> core(Methods ctx){
    var inferrableAST= ToInference.of(ctx); // Phase 4: Desugar
    inferrableAST = ctx.registerTypeHeadersAndReturnRoots(inferrableAST); // Phase 5: Build Synthetic type table inside ctx
    var coreAST= InjectionSteps.steps(ctx, inferrableAST);  // Phase 6: Inference
    TypeSystem.allOk(coreAST, ctx.p(), ctx.other()); //Phase 7: type checking
    return coreAST;
  }
  public Map<String,Map<String,String>> parseRankFiles(Map<String,Ref> ranks, Comparator<Ref> c){
    var pkgs= Push.of(List.copyOf(ranks.keySet()), "base");
    var parsed= parseFiles(List.copyOf(ranks.values()));
    record Key(String target, String in){}
    record Cand(Ref uri, String target, String in, String out){
    @Override public String toString(){
      var f= PrettyFileName.displayFileName(uri.fearURI());
      return " - "+f+"\n"
           +"   \"map  "+in+"  as  "+out+"  in  "+target+";\"";
    }}
    var byKey= parsed.entrySet().stream()
      .flatMap(e -> e.getValue().maps().stream().map(m -> new Cand(e.getKey(), m.target(), m.in(), m.out())
      )).collect(Collectors.groupingBy(x -> new Key(x.target(), x.in())));
    var res= new HashMap<String,HashMap<String,String>>();
    var chosen= new TreeMap<String,ArrayList<Cand>>();
    var sorted= byKey.entrySet().stream().sorted(Comparator.comparing(e -> e.getKey().target()+" "+e.getKey().in())).toList();
    for (var e : sorted){
      var k= e.getKey();
      var cs= e.getValue();
      var best= Collections.max(cs, Comparator.comparing(Cand::uri, c));
      var bests= cs.stream().filter(x -> c.compare(x.uri(), best.uri()) == 0).toList();
      // What to do if two different rank files with the SAME RANK give the SAME MAPPING? Here we are tolerant.
      var conflicting= bests.stream().map(Cand::out).distinct().count() != 1;
      var err= new WellFormednessErrors(k.target());
      if (conflicting){ throw err.mapConflict(k.in(), bests.stream().map(Object::toString).toList()); }
      if (k.target().equals("base")){ throw err.mapInBase(k.in(), best.out(), best.toString()); }
      if (!ranks.containsKey(k.target())){ throw err.mapInMissingPackage(k.in(), best.out(), best.toString(), ranks.keySet().stream().sorted().toList()); }
      if (pkgs.contains(k.in())){ throw err.mapOfAnExistingPackage(k.in(), best.out(), best.toString()); }
      if (!pkgs.contains(best.out())){ throw err.mapToMissingPackage(k.in(), best.out(), best.toString(), pkgs.stream().sorted().toList()); }
      if (best.out().equals(k.target())){ throw err.mapToItself(k.in(), best.toString()); }
      var outRank= ranks.get(best.out());
      var targetRank= ranks.get(k.target());
      var lower= outRank == null || c.compare(outRank, targetRank) < 0;
      if (!lower){ throw err.mapToNotLowerRank(k.in(), best.out(), best.toString(), targetRank, outRank, c.compare(outRank, targetRank) == 0); }
      res.computeIfAbsent(k.target(), _ -> new HashMap<>()).put(k.in(), best.out());
      chosen.computeIfAbsent(k.target()+"."+best.out(), _ -> new ArrayList<>()).add(best);
    }
    var shared= chosen.values().stream().filter(cs -> cs.size() > 1).findFirst();
    shared.ifPresent(cs -> { throw new WellFormednessErrors(cs.getFirst().target()).mapToATargetOfAnotherMap(cs.getFirst().out(), cs.stream().map(Object::toString).toList()); });
    ranks.forEach((pkg, f) -> usesOnlyLowerRanks(pkg, parsed.get(f).uses(), res.getOrDefault(pkg, new HashMap<>()), ranks, c));
    return res.entrySet().stream().collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, e -> Map.copyOf(e.getValue())));
  }
  private void usesOnlyLowerRanks(String pkg, List<FileFull.Use> uses, Map<String,String> map, Map<String,Ref> ranks, Comparator<Ref> c){
    for (var u : uses){
      var p= map.getOrDefault(u.in().pkgName(), u.in().pkgName());
      var other= ranks.get(p);
      var allowed= p.equals(pkg) || other == null || c.compare(other, ranks.get(pkg)) < 0;
      if (!allowed){ throw new WellFormednessErrors(pkg).useOfNotLowerRank(u.in(), p, ranks.get(pkg), other, c.compare(other, ranks.get(pkg)) == 0); }
    }
  }
  Map<Ref,FileFull> parseFiles(List<Ref> files){
    var all= new LinkedHashMap<Ref,FileFull>();
    for (var u : files){ all.put(u, Parse.from(u.fearURI(), u.loadString())); }
    return Collections.unmodifiableMap(all);
  }
  Package mergeToPackage(String pkgName, Map<Ref,FileFull> raw, Map<String,String> override, OtherPackages other){
    assert !raw.isEmpty();
    var err= new WellFormednessErrors(pkgName);
    var headPkg= findHeadUri(err, raw.keySet());
    raw.entrySet().stream()
      .filter(e -> !e.getKey().equals(headPkg) && !e.getValue().noDirectives())
      .forEach(e -> { throw err.notClean(e.getKey(), e.getValue()); });
    var head= raw.get(headPkg);
    var ds= raw.values().stream()
      .flatMap(f -> f.decs().stream())
      .sorted().toList();
    var names= DeclaredNames.of(pkgName, ds, head.uses().stream().map(FileFull.Use::out).collect(Collectors.toUnmodifiableSet()));
    return makePackage(pkgName, directives(err, override, head.uses(), other), head.uses(), ds, names);
  }
  public Function<TName,String> names(String pkgName, Map<String,String> override, List<Ref> files, OtherPackages other){
    var err= new WellFormednessErrors(pkgName);
    var head= findHeadUri(err, Set.copyOf(files));
    var map= directives(err, override, Parse.from(head.fearURI(), head.loadString()).uses(), other);
    return t -> Package.nameOf(pkgName, map, t);
  }
  private Map<String,String> directives(WellFormednessErrors err, Map<String,String> override, List<FileFull.Use> uses, OtherPackages other){
    var map= new HashMap<>(override);
    accUses(err, map, uses, other);
    return Collections.unmodifiableMap(map);
  }
  Package makePackage(String name, Map<String,String> map, List<FileFull.Use> uses, List<Declaration> decs, DeclaredNames names){
    return new Package(name, map, uses, decs, names, new Package.Logger(false, null));//this method exists to change logger in mocking
  }
  //map a as b in c //inside c, a written a stands for b
  private void accUses(WellFormednessErrors err, HashMap<String,String> map, List<FileFull.Use> uses, OtherPackages other){
    Collection<TName> otherDom= uses.isEmpty() ? List.of() : other.dom();
    for (var u : uses){
      if (u.in().pkgName().isEmpty()){ throw err.useNotFullyQualified(u.in()); }
      var named= Package.mapTo(err.pkgName(), map, u.in().pkgName());
      if (named.isPresent()){ throw err.useOfAMapTarget(u.in(), named.get()); }
      var p= map.getOrDefault(u.in().pkgName(), u.in().pkgName());
      if (p.equals(err.pkgName())){ throw err.useOfTheCurrentPackage(u.in(), p); }
      var in= p+"."+u.in().simpleName();
      map.put(u.out(), in);
      if (otherDom.stream().noneMatch(e -> e.s().equals(in))){ throw err.unknownUseHead(u.in(), p); }
    }//map a as b in c + use a.F as aF will replace aF with b.F
  }
  private Ref findHeadUri(WellFormednessErrors err, Set<Ref> uris){
    assert nonNull(uris);
    assert validate(err.pkgName(), "", _pkgName);
    var heads= uris.stream().filter(this::isHeadUri).toList();
    if (heads.size() == 1){ return heads.getFirst(); }
    throw err.expectedSingleUriForPackage(heads);
  }
  private boolean isHeadUri(Ref u){
    var name= Fs.fileNameWithExtension(u.fearPath());
    var dot= name.lastIndexOf('.');
    return dot > 0 && name.substring(0, dot).startsWith("_rank_");
  }
}