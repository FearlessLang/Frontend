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
    var testPkg= makePackage(pkgName, all.map(), all.writtenIn(), all.uses(), testAST.decs().stream().sorted().toList(), all.names());
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
    record Cand(Ref uri, FileFull.Map m){
      @Override public String toString(){ return "- \""+m+";\"; written in "+writtenIn(uri); }
    }
    var byKey= parsed.entrySet().stream()
      .flatMap(e -> e.getValue().maps().stream().map(m -> new Cand(e.getKey(), m)))
      .collect(Collectors.groupingBy(x -> x.m().target()+" "+x.m().in(), TreeMap::new, Collectors.toList()));
    var winners= new ArrayList<Cand>();
    for (var cs : byKey.values()){
      var best= Collections.max(cs, Comparator.comparing(Cand::uri, c));
      var bests= cs.stream().filter(x -> c.compare(x.uri(), best.uri()) == 0).toList();
      var m= best.m();
      // What to do if two different rank files with the SAME RANK give the SAME MAPPING? Here we are tolerant.
      var conflicting= bests.stream().map(x -> x.m().out()).distinct().count() != 1;
      var err= new WellFormednessErrors(m.target());
      if (conflicting){ throw err.mapConflict(m.in(), bests.stream().map(Object::toString).toList()); }
      if (m.target().equals("base")){ throw err.mapInBase(best.toString()); }
      if (!ranks.containsKey(m.target())){ throw err.mapToMissingFolder("applies to source code inside", m.target(), best.toString(), ranks.keySet().stream().sorted().toList()); }
      if (pkgs.contains(m.in())){ throw err.mapOfAnExistingPackage(m.in(), best.toString()); }
      if (!pkgs.contains(m.out())){ throw err.mapToMissingFolder("refers to the code inside", m.out(), best.toString(), pkgs.stream().sorted().toList()); }
      if (m.out().equals(m.target())){ throw err.mapToItself(best.toString()); }
      var outRank= ranks.get(m.out());
      var cmp= outRank == null ? -1 : c.compare(outRank, ranks.get(m.target()));
      if (cmp >= 0){ throw err.mapToNotLowerRank(m.out(), best.toString(), ranks.get(m.target()), outRank, cmp == 0); }
      var overridden= cs.stream().filter(x -> c.compare(x.uri(), best.uri()) < 0 && !x.m().out().equals(m.out())).toList();
      var expected= overridden.stream().map(x -> x.m().out()).distinct().sorted().toList();
      var wrong= bests.stream().filter(x -> !x.m().insteadOf().stream().sorted().toList().equals(expected)).findFirst();
      if (wrong.isPresent()){ throw err.insteadOfMismatch(wrong.get().toString(), overridden.stream().map(Object::toString).toList(), new FileFull.Map(m.in(), m.out(), m.target(), expected)); }
      winners.add(best);
    }
    var shared= winners.stream().collect(Collectors.groupingBy(x -> x.m().target()+"."+x.m().out(), TreeMap::new, Collectors.toList())).values().stream().filter(cs -> cs.size() > 1).findFirst();
    if (shared.isPresent()){ throw new WellFormednessErrors(shared.get().getFirst().m().target()).mapToATargetOfAnotherMap(shared.get().getFirst().m().out(), shared.get().stream().map(Object::toString).toList()); }
    ranks.forEach((pkg, f) -> usesOnlyLowerRanks(pkg, parsed.get(f).uses(), ranks, c));
    return Map.copyOf(winners.stream().collect(Collectors.groupingBy(x -> x.m().target(), Collectors.toUnmodifiableMap(x -> x.m().in(), x -> x.m().out()+" "+writtenIn(x.uri())))));
  }
  private static String writtenIn(Ref uri){ return PrettyFileName.displayFileName(uri.fearURI()); }
  private void usesOnlyLowerRanks(String pkg, List<FileFull.Use> uses, Map<String,Ref> ranks, Comparator<Ref> c){
    for (var u : uses){
      var p= u.in().pkgName();
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
    var writtenIn= writtenIn(override);
    var err= new WellFormednessErrors(pkgName, Map.of(), writtenIn, new LinkedHashSet<>());
    var headPkg= findHeadUri(err, raw.keySet());
    raw.entrySet().stream()
      .filter(e -> !e.getKey().equals(headPkg) && !e.getValue().noDirectives())
      .forEach(e -> { throw err.notClean(e.getKey(), e.getValue()); });
    var head= raw.get(headPkg);
    var ds= raw.values().stream()
      .flatMap(f -> f.decs().stream())
      .sorted().toList();
    var names= DeclaredNames.of(pkgName, ds, head.uses().stream().map(FileFull.Use::out).collect(Collectors.toUnmodifiableSet()));
    return makePackage(pkgName, directives(err, override, head.uses(), other), writtenIn, head.uses(), ds, names);
  }
  public Function<TName,String> names(String pkgName, Map<String,String> override, List<Ref> files, OtherPackages other){
    var err= new WellFormednessErrors(pkgName, Map.of(), writtenIn(override), new LinkedHashSet<>());
    var head= findHeadUri(err, Set.copyOf(files));
    var map= directives(err, override, Parse.from(head.fearURI(), head.loadString()).uses(), other);
    return t -> Package.nameOf(pkgName, map, t);
  }
  private Map<String,String> directives(WellFormednessErrors err, Map<String,String> override, List<FileFull.Use> uses, OtherPackages other){
    var map= new HashMap<String,String>();
    override.forEach((k, v) -> map.put(k, v.split(" ")[0]));
    accUses(err, map, uses, other);
    return Collections.unmodifiableMap(map);
  }
  private static Map<String,String> writtenIn(Map<String,String> override){
    return override.entrySet().stream().collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, e -> e.getValue().substring(e.getValue().indexOf(' ')+1)));
  }
  Package makePackage(String name, Map<String,String> map, Map<String,String> writtenIn, List<FileFull.Use> uses, List<Declaration> decs, DeclaredNames names){
    return new Package(name, map, writtenIn, uses, decs, names, new Package.Logger(false, null));//this method exists to change logger in mocking
  }
  //map a as _b in _c //inside _c, the package name a stands for the code inside _b
  private void accUses(WellFormednessErrors err, HashMap<String,String> map, List<FileFull.Use> uses, OtherPackages other){
    var otherDom= other.dom();
    for (var u : uses){
      if (u.in().pkgName().isEmpty()){ throw err.useNotFullyQualified(u.in()); }
      if (map.containsValue(u.in().pkgName())){ throw err.useOfAMapTarget(u.in(), WellFormednessErrors.written(map).get(u.in().pkgName()), Package.visible(map, otherDom)); }
      var p= map.getOrDefault(u.in().pkgName(), u.in().pkgName());
      if (p.equals(err.pkgName())){ throw err.useOfTheCurrentPackage(u.in()); }
      var in= p+"."+u.in().simpleName();
      map.put(u.out(), in);
      if (otherDom.stream().noneMatch(e -> e.pkgName().equals(p))){ throw err.useOfMissingPackage(u.in(), Package.visible(map, otherDom)); }
      if (otherDom.stream().noneMatch(e -> e.s().equals(in))){ throw err.unknownUseHead(u.in(), map); }
    }//map a as _b in _c + use a.F as AF will replace AF with b.F
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