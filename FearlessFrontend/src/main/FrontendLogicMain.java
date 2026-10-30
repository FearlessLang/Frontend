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
    record Key(String target, String in){}
    record Cand(Ref uri, FileFull.Map m){
      @Override public String toString(){ return "- \""+m+";\"; written in "+writtenIn(uri); }
    }
    var byKey= parsed.entrySet().stream()
      .flatMap(e -> e.getValue().maps().stream().map(m -> new Cand(e.getKey(), m)))
      .collect(Collectors.groupingBy(x -> new Key(x.m().target(), x.m().in())));
    var res= new HashMap<String,HashMap<String,Cand>>();
    var chosen= new TreeMap<String,ArrayList<Cand>>();
    var sorted= byKey.entrySet().stream().sorted(Comparator.comparing(e -> e.getKey().target()+" "+e.getKey().in())).toList();
    for (var e : sorted){
      var k= e.getKey();
      var cs= e.getValue();
      var best= Collections.max(cs, Comparator.comparing(Cand::uri, c));
      var bests= cs.stream().filter(x -> c.compare(x.uri(), best.uri()) == 0).toList();
      var out= best.m().out();
      // What to do if two different rank files with the SAME RANK give the SAME MAPPING? Here we are tolerant.
      var conflicting= bests.stream().map(x -> x.m().out()).distinct().count() != 1;
      var err= new WellFormednessErrors(k.target());
      if (conflicting){ throw err.mapConflict(k.in(), bests.stream().map(Object::toString).toList()); }
      if (k.target().equals("base")){ throw err.mapInBase(best.toString()); }
      if (!ranks.containsKey(k.target())){ throw err.mapInMissingPackage(best.toString(), ranks.keySet().stream().sorted().toList()); }
      if (pkgs.contains(k.in())){ throw err.mapOfAnExistingPackage(k.in(), best.toString()); }
      if (!pkgs.contains(out)){ throw err.mapToMissingPackage(out, best.toString(), pkgs.stream().sorted().toList()); }
      if (out.equals(k.target())){ throw err.mapToItself(best.toString()); }
      var outRank= ranks.get(out);
      var targetRank= ranks.get(k.target());
      var lower= outRank == null || c.compare(outRank, targetRank) < 0;
      if (!lower){ throw err.mapToNotLowerRank(out, best.toString(), targetRank, outRank, c.compare(outRank, targetRank) == 0); }
      var overridden= cs.stream().filter(x -> c.compare(x.uri(), best.uri()) < 0 && !x.m().out().equals(out)).toList();
      var expected= overridden.stream().map(x -> x.m().out()).distinct().sorted().toList();
      var wrong= bests.stream().filter(x -> !x.m().insteadOf().stream().distinct().sorted().toList().equals(expected)).findFirst();
      if (wrong.isPresent()){ throw err.insteadOfMismatch(wrong.get().toString(), overridden.stream().map(Object::toString).toList(), new FileFull.Map(k.in(), out, k.target(), expected)); }
      res.computeIfAbsent(k.target(), _ -> new HashMap<>()).put(k.in(), best);
      chosen.computeIfAbsent(k.target()+"."+out, _ -> new ArrayList<>()).add(best);
    }
    var shared= chosen.values().stream().filter(cs -> cs.size() > 1).findFirst();
    shared.ifPresent(cs -> { throw new WellFormednessErrors(cs.getFirst().m().target()).mapToATargetOfAnotherMap(cs.getFirst().m().out(), cs.stream().map(Object::toString).toList()); });
    Function<String,Map<String,String>> outs= pkg -> res.getOrDefault(pkg, new HashMap<>()).entrySet().stream()
      .collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, x -> x.getValue().m().out()));
    ranks.forEach((pkg, f) -> usesOnlyLowerRanks(pkg, parsed.get(f).uses(), outs.apply(pkg), ranks, c));
    return res.entrySet().stream().collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, e -> e.getValue().entrySet().stream()
      .collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, x -> x.getValue().m().out()+" "+writtenIn(x.getValue().uri())))));
  }
  private static String writtenIn(Ref uri){ return PrettyFileName.displayFileName(uri.fearURI()); }
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
    override.forEach((in, v) -> map.put(in, v.substring(0, v.indexOf(' '))));
    accUses(err, map, uses, other);
    return Collections.unmodifiableMap(map);
  }
  private static Map<String,String> writtenIn(Map<String,String> override){
    return override.entrySet().stream().collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, e -> e.getValue().substring(e.getValue().indexOf(' ')+1)));
  }
  Package makePackage(String name, Map<String,String> map, Map<String,String> writtenIn, List<FileFull.Use> uses, List<Declaration> decs, DeclaredNames names){
    return new Package(name, map, writtenIn, uses, decs, names, new Package.Logger(false, null));//this method exists to change logger in mocking
  }
  //map a as b in c //inside c, a written a stands for b
  private void accUses(WellFormednessErrors err, HashMap<String,String> map, List<FileFull.Use> uses, OtherPackages other){
    Collection<TName> otherDom= uses.isEmpty() ? List.of() : other.dom();
    for (var u : uses){
      if (u.in().pkgName().isEmpty()){ throw err.useNotFullyQualified(u.in()); }
      var named= Package.mapTo(err.pkgName(), map, u.in().pkgName());
      if (named.isPresent()){ throw err.useOfAMapTarget(u.in(), named.get(), Package.visible(err.pkgName(), map, otherDom)); }
      var p= map.getOrDefault(u.in().pkgName(), u.in().pkgName());
      if (p.equals(err.pkgName())){ throw err.useOfTheCurrentPackage(u.in(), p); }
      var in= p+"."+u.in().simpleName();
      map.put(u.out(), in);
      if (otherDom.stream().noneMatch(e -> e.pkgName().equals(p))){ throw err.useOfMissingPackage(u.in(), Package.visible(err.pkgName(), map, otherDom)); }
      if (otherDom.stream().noneMatch(e -> e.s().equals(in))){ throw err.unknownUseHead(u.in(), map); }
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