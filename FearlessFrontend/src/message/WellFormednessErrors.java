package message;

import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.X;
import fearlessFullGrammar.TName;
import fearlessParser.Parser;
import fearlessParser.RC;
import inference.E;
import inference.IT;
import inference.M;
import inject.Methods.Agreement;
import metaParser.Message;
import metaParser.NameSuggester;
import metaParser.PrettyFileName;
import metaParser.Span;
import naming.FreshPrefix;
import utils.Bug;

public record WellFormednessErrors(Err err) {
  public WellFormednessErrors(String pkgName){
    this(new Err(() -> new CompactPrinter(pkgName,Map.of()), new StringBuilder()));
  }
  public FearlessException notClean(URI uri, FileFull f){
    return Code.WellFormedness.of(() -> buildMessageNotClean(f))
      .addSpan(new Span(uri,0,0,1,1));
  }
  private String buildMessageNotClean(FileFull f){
    List<String> bullets= new ArrayList<>();
    if (!f.maps().isEmpty()){ bullets.add("maps: " + previewList(f.maps(), 5)); }
    if (!f.uses().isEmpty()){ bullets.add("uses: " + previewList(f.uses(), 8)); }
    if (!f.role().isEmpty()){ bullets.add("role: " + f.role().get()); }
    StringBuilder sb= new StringBuilder()
      .append("File is not the package head, but contains package head directives.\n")
      .append("It should not contain any directives like maps, uses or role.\n");
    assert !bullets.isEmpty();
    sb.append("Found non-empty:\n");
    bullets.forEach(b->sb.append("  - ").append(b).append('\n'));
    return sb.toString();
  }
  private String previewList(List<?> c, int limit){
    StringBuilder sb = new StringBuilder();
    int i = 0;
    for (var x : c){
      if (i > 0) sb.append(", ");
      if (i == limit){
        sb.append("...").append(" (size=").append(c.size()).append(')');
        return sb.toString();
      }
      sb.append(String.valueOf(x));
      i++;
    }
    return sb.toString();
  }
  
  public FearlessException expectedSingleUriForPackage(List<URI> heads, String pkgName){
    return Code.WellFormedness.of(() -> buildMessageSingleUriForPackage(heads, pkgName));
  }
  private String buildMessageSingleUriForPackage(List<URI> heads, String pkgName){
    if (heads.isEmpty()){
      return "No package head file found for package " + Message.displayString(pkgName) + ".\n"
      + "Each package must have exactly one source file whose name matches the package name.\n"
      + "For example, for package " + Message.displayString(pkgName) + " you would typically have a file named\n"
      + "    " + pkgName + ".fear\n"
      + "in some folder inside the project folder.\n";
    }
    StringBuilder sb= new StringBuilder()
      .append("Ambiguous package head file for package \"")
      .append(pkgName)
      .append("\".\n")
      .append("Found ")
      .append(heads.size())
      .append(" files that look like package head candidates:\n");
    heads.forEach(u->sb
      .append("  - ")
      .append(PrettyFileName.displayFileName(u))
      .append("\n"));
    sb.append("There must be exactly one source file whose name matches the package name.\n")
      .append("Rename or remove the extra files so that only one file is named \"")
      .append(pkgName)
      .append(".fear\".");
    return sb.toString();
  }
  public FearlessException noRole(URI uri, FileFull f){
    return Code.WellFormedness.of(() -> buildMessageNoRole(uri, f)).addSpan(new Span(uri,0,0,1,1));
  }
  private String buildMessageNoRole(URI uri, FileFull f){
    return new StringBuilder()
      .append("Missing role declaration in package head file.\n")
      .append("Every package must declare its role: base, core, driver, worker, framework, accumulator, tool, or app.\n")
      .append("The package head file is the file whose name matches the package name.\n")
      .append("Add a top-level role line to that file. For example:\n")
      .append("package myCoolGame;\n")
      .append("role app999;\n")
      .append("use base.Main as Main;\n")
      .append("MyGame:Main{s->Debug#(`Hello world`)}\n")
      .append("\n")
      .append("As a rule of thumb: final applications use appNNN; shared libraries often use workerNNN or frameworkNNN.\n")
      .toString();
  }
  public FearlessException usedDeclaredNameClash(String pkgName, Set<TName> names, Set<String> keySet){
    for (TName n:names){ 
      var clash= keySet.contains(n.s());
      if (!clash){ continue; }
      return Code.WellFormedness.of(
        "Name clash: name "+Message.displayString(n.s())+" is declared in package "+Message.displayString(pkgName)+".\n"
        +"Name "+Message.displayString(n.s())+" is also used in a \"use\" directive.\n"
        ).addFrame("a type name",Parser.span(n.pos(),n.s().length()));
    }
    throw Bug.unreachable();
  }
  public FearlessException usedUndeclaredName(TName tn, String contextPkg, List<TName> scope, List<TName> all){
    return new UndeclaredNameContext(tn, contextPkg, scope, all,
      all.stream().map(TName::pkgName).filter(p -> !p.isEmpty()).distinct().sorted().toList(),
      tn.pkgName(),tn.simpleName()
      ).build();
  }
  private record UndeclaredNameContext(
      TName tn, String contextPkg, List<TName> scope, List<TName> all,
      List<String> allPkgs, String typedPkg, String typedSimple){
    FearlessException build(){
      return pkgDoesNotExist()
        .or(this::otherArity)
        .orElseGet(this::undeclaredInPkg);
    }
    private Optional<FearlessException> pkgDoesNotExist(){
      if (typedPkg.isEmpty()){ return Optional.empty(); }
      if (allPkgs.contains(typedPkg)){ return Optional.empty(); }
      StringBuilder msg= new StringBuilder()
        .append("Package ")
        .append(Message.displayString(typedPkg))
        .append(" does not exist.\n");
        NameSuggester.suggest(typedPkg, allPkgs,(_,cs,best)->{
          best.ifPresent(b -> msg
            .append("Did you mean ")
            .append(Message.displayString(b))
            .append(" ?\n"));
          msg.append(Join.of(
            cs.stream().map(Message::displayString),
            "Visible packages: ",", ",".\n"));
          return null;
          });
      return Optional.of(make(msg));
    }
    private <A,R> List<R> userMap(Function<A,R> f,Stream<A> s){ return s.map(f).distinct().sorted().toList(); }

    private Optional<FearlessException> otherArity(){
      List<TName> candidates= typedPkg.isEmpty() ? scope : typesInPkg(typedPkg);
      var arities= userMap(TName::arity,candidates.stream()
        .filter(t -> t.simpleName().equals(typedSimple)));
      assert !arities.contains(tn.arity());
      if (arities.isEmpty()){ return Optional.empty(); }
      String targetPkg = typedPkg.isEmpty() ? contextPkg : typedPkg;
      StringBuilder msg= new StringBuilder()
        .append("Name ").append(Message.displayString(typedSimple))
        .append(" is not declared with ").append(tn.arity())
        .append(" type parameter(s) in package ")
        .append(Message.displayString(targetPkg))
        .append(".\n")
        .append("Name ")
        .append(Message.displayString(typedSimple))
        .append(" is only declared with ");
      if (arities.size() == 1){ msg.append(arities.getFirst()).append(" type parameter(s)"); }
      else{ msg.append(Join.of(arities,"the following numbers of type parameters: ",", ","")); }
      msg.append(".\nDid you accidentally add or omit a type parameter?\n");
      return Optional.of(make(msg));
    }
    private FearlessException undeclaredInPkg(){
      List<TName> inPkg= typedPkg.isEmpty() ? scope : typesInPkg(typedPkg);
      var simpleInPkg= simpleNames(inPkg);
      StringBuilder msg= new StringBuilder()
        .append("Type ")
        .append(Message.displayString(typedSimple))
        .append(" is not declared in package ")
        .append(relevantPkgMsg())
        .append(".\n")
        .append(NameSuggester.suggest(typedSimple, simpleInPkg));
      if (!typedPkg.isEmpty()){ addOtherPkgNotePkgExplicit(msg); return make(msg); }
      var noBestLocal= NameSuggester.bestName(typedSimple, simpleInPkg).isEmpty();
      if (noBestLocal){ addOtherPkgNotePkgImplicit(msg); }
      return make(msg);
    }
    private String relevantPkgMsg(){
      if (!typedPkg.isEmpty()){ return Message.displayString(typedPkg); }
      return Message.displayString(contextPkg)+" and is not made visible via \"use\"";
    }
    
    private List<TName> typesInPkg(String pkg){
      return all.stream().filter(t -> t.pkgName().equals(pkg)).toList();
    }
    private List<String> simpleNames(List<TName> xs){ return userMap(TName::simpleName,xs.stream()); }
    private void addOtherPkgNotePkgExplicit(StringBuilder msg){
      var sameSimpleOther= userMap(TName::s, all.stream()
        .filter(t -> !t.pkgName().equals(typedPkg))
        .filter(t -> t.simpleName().equals(typedSimple)));
      addOptionsList(sameSimpleOther, msg);
    }
    private void addOtherPkgNotePkgImplicit(StringBuilder msg){
      var other= all.stream().filter(t -> !t.pkgName().equals(contextPkg)).toList();
      if (other.isEmpty()){ return; }
      var simpleCandidates= userMap(TName::simpleName,other.stream());
      NameSuggester.bestName(typedSimple, simpleCandidates)
        .ifPresent(bestSimple->addOptionsList(
          userMap(TName::s,all.stream().filter(t -> t.simpleName().equals(bestSimple))),
          msg));
    }
    void addOptionsList(List<String> ss, StringBuilder msg){
      if (ss.isEmpty()){ return; }
      msg.append(Join.of(
        ss.stream().map(Message::displayString),
        "Did you mean "," or "," ?\n"+addUse));
    }    
    private static String addUse="Add a \"use\" or write the fully qualified name.\n";
    private FearlessException make(StringBuilder msg){
      trimTrailingNewline(msg);
      return Code.WellFormedness.of(msg.toString()).addFrame("a type name", at()); }
    private Span at(){ return Parser.span(tn.pos(), tn.s().length()); }
  }
  static private void trimTrailingNewline(StringBuilder sb){
    int len= sb.length();
    if (len > 0 && sb.charAt(len - 1) == '\n'){ sb.setLength(len - 1); }
  }
  public FearlessException unknownUseHead(TName tn){
    var at= Parser.span(tn.pos(),tn.s().length());
    return Code.WellFormedness.of(
      "\"use\" directive refers to undeclared name: type "
      +Message.displayString(tn.simpleName())
      +" is not declared in package " + Message.displayString(tn.pkgName()) + ".\n"
    ).addFrame("package header", at);
  }
 public FearlessException genericTypeVariableShadowTName(String pkgName, Map<TName, Set<X>> allXs, List<String> allNames, Set<String> use){
   var mergeAllXs= allXs.values().stream().flatMap(Set::stream).toList();
   for (var n : mergeAllXs){
     var clashDec= allNames.contains(n.name());
     var clashUse= use.contains(n.name());
     if (clashDec || clashUse){ return shadowMsg(pkgName,n,clashUse); }
   }
   throw Bug.unreachable();
 }
 private FearlessException shadowMsg(String pkgName, T.X n, boolean use){
   return Code.WellFormedness.of(
     "Type parameter " + Message.displayString(n.name())
     +" is declared in package \"" + pkgName + "\".\n"
     + "Name "+Message.displayString(n.name())+" is also used "
     + (use?"in a \"use\" directive.\n":"as a type name.\n")
     ).addFrame("a type name",n.span().inner);
  }

 public FearlessException duplicatedBound(List<RC> es, T.X n){
   RC dup= es.stream()
     .filter(e->es.stream().filter(ei->ei.equals(e)).count() > 1)
     .findFirst().get();
   return Code.WellFormedness.of(
       "Duplicate reference capability in the type parameter "+Message.displayString(n.name())+".\n"
       + "Reference capability "+Message.displayString(dup.name())+" is repeated.\n"
       ).addSpan(n.span().inner);
    }
  public FearlessException duplicatedName(TName name) {
    return Code.WellFormedness.of(
      "Duplicate type declaration for "+Err.staticTypeDecName(name)+".\n"
      ).addFrame("a type name",Parser.span(name.pos(),name.s().length()));
  }
  public FearlessException circularImplements(Map<TName,E.Literal> rem){
    TName name = findCycleNode(rem);
    return Code.WellFormedness.of(
      "Circular implementation relation found involving "+Err.staticTypeDecName(name)+".\n"
      ).addFrame("type declarations",Parser.span(name.pos(),name.s().length()));
  }
  private TName findCycleNode(Map<TName,E.Literal> rem){
    var color= new HashMap<TName,Integer>(rem.size());
    for (var k : rem.keySet()){
      var hit= dfs(rem,k,color);
      if (hit != null){ return hit; }
    }
    throw Bug.unreachable();
  }
  private TName dfs(Map<TName,E.Literal> rem,TName u,Map<TName,Integer> color){
    Integer cu= color.get(u);
    if (cu != null){ return cu == 1 ? u : null; }
    color.put(u,1);
    for (var c:rem.get(u).cs()){
      if (!rem.containsKey(c.name())){ continue; }
      var hit= dfs(rem,c.name(),color);
      if (hit != null){ return hit; }
    }
    color.put(u,2);
    return null;
  }
  public FearlessException noSourceToInferFrom(E.Literal origin, M m){
    var empty= m.sig().m().isEmpty();
    var size= m.sig().ts().size();
    if (empty){ return Code.WellFormedness.of(
      "Cannot infer signature and name for a method with "+size+" parameters.\n"
    + "No supertype has a method with "+size+" parameters.\n"
      ).addSpan(m.sig().span().inner)
      .addFrame(err.expRepr(origin), origin.span().inner); }
    var name= Err.methodSig(m.sig().m().get());
    return Code.WellFormedness.of(
      "Cannot infer signature of method "+name+".\n"
    + "No supertype has a method named "+name+" with "+size+" parameters.\n"
      ).addSpan(m.sig().span().inner)
      .addFrame(err.expRepr(origin), origin.span().inner);
  }
  public String refCapDisagreement(){ return "Reference capability disagreement"; }
  public String retTypeDisagreement(){ return "Return type disagreement"; }
  public String argTypeDisagreement(int i){ return "Type disagreement about argument "+i; }
  public FearlessException noAgreement(Agreement at, FreshPrefix fresh, List<?> res, String msg){
    return Code.WellFormedness.of(
      msg+ " for method "
    + Err.methodSig(at.mName())+" with "+at.mName().arity()+" parameters.\n"
    + Join.of(
        res.stream().map(o->Err.disp(o)),
        "Different options are present in the implemented types: ",", ",".\n")
    + Err.up(err.expRepr(at.lit()))+" must declare a method "
    + Err.methodSig(at.mName())+" explicitly choosing the desired option.\n"
    ).addFrame(err.expRepr(at.lit()), at.span());
  }
  public FearlessException methodGenericArityDisagreementBetweenSupers(Agreement at, FreshPrefix fresh, List<List<B>> res){
    return Code.WellFormedness.of(
    "The number of type parameters disagrees for method "
    + Err.methodSig(at.mName())
    + " with " + at.mName().arity() + " parameters.\n"
    + Join.of(
        res.stream().map(o->Err.disp(o)),
        "Different options are present in the implemented types: ",", ",".\n")
    + Err.up(err.expRepr(at.lit()))
    + " cannot implement all of those types.\n"
    ).addFrame(err.expRepr(at.lit()), at.span());
  }
  public FearlessException methodGenericArityDisagreesWithSupers(Agreement at, FreshPrefix fresh, int userArity, int superArity, List<B> userBs, List<B> superBs){
    String sB= Err.disp(superBs.stream().map(b->new B("-",b.rcs())).toList());
    //TODO: this is inconsistent with this other line String sB= Err.disp(new B("-",s.rcs()));
    //Report on all of them or only the conflicting one??
    return Code.WellFormedness.of(
      "Invalid method implementation for "+err.methodSig(at.lit(),at.mName())+".\n"
    + "The method " + Err.methodSig(at.mName())
    + " declares " + userArity + " type parameter(s), "
    + "but supertypes declare " + superArity + ".\n"
    + "Local declaration: " + Err.disp(userBs) + ".\n"
    + "From supertypes: " + sB + ".\n"
    + "Change the local number of type parameters to "
    + superArity + ", or adjust the supertypes.\n" 
    ).addFrame(err.expRepr(at.lit()), at.span());
  }
  public FearlessException methodBsDisagreementBetweenSupers(Agreement at, FreshPrefix fresh, List<List<B>> res){
    assert res.size() >= 2;
    int n= res.getFirst().size();
    assert res.stream().allMatch(bs->bs.size() == n);
    int i= firstRcsDisagreementIndex(res);
    String opts= Join.of(
      res.stream().map(bs->Err.disp(bs.get(i))).distinct().sorted(),
      "", " and ", ".\n");
    String m= Err.methodSig(at.mName());
    return Code.WellFormedness.of(
      "Invalid method implementation for "+err.methodSig(at.lit(), at.mName())+".\n"
    + "Supertypes disagree on the capability bounds for type parameter "+(i+1)+" of "+m+".\n"
    + "Type parameter names may differ across supertypes; only the position matters.\n"
    + "Different supertypes declare: " + opts
    + Err.up(err.expRepr(at.lit()))+" cannot implement all of those supertypes.\n"
    + "Make the supertypes agree on these bounds, or remove one of the conflicting supertypes.\n"
    ).addFrame(err.expRepr(at.lit()), at.span());
  }
  public FearlessException methodBsDisagreesWithSupers(Agreement at, FreshPrefix fresh, List<B> userBs, List<B> superBs){
    assert userBs.size() == superBs.size();
    int i= firstRcsDisagreementIndex(List.of(userBs, superBs));
    var u= userBs.get(i);
    var s= superBs.get(i);
    String m= Err.methodSig(at.mName());
    String uB= Err.disp(u);
    String sB= Err.disp(new B("-",s.rcs()));
    return Code.WellFormedness.of(
      "Invalid method implementation for "+err.methodSig(at.lit(), at.mName())+".\n"
    + "The local declaration uses different capability bounds than the supertypes for type parameter "+(i+1)+" of "+m+".\n"
    + "Local: "+uB+".\n"
    + "From supertypes: "+sB+".\n"
    + "The parameter name may differ; only the position matters.\n"
    + "Change the local bounds to match the supertypes, or adjust the supertypes.\n"
    ).addFrame(err.expRepr(at.lit()), at.span());
  }
  private int firstRcsDisagreementIndex(List<List<B>> res){
    return IntStream.range(0, res.getFirst().size())
      .filter(i->{
        var r0= res.getFirst().get(i).rcs();
        return !res.stream().allMatch(bs->bs.get(i).rcs().equals(r0));
      })
      .findFirst().getAsInt();
  }
  public FearlessException ambiguousImpl(E.Literal origin, FreshPrefix fresh, boolean abs, M m, List<inference.M.Sig> options){
    return Code.WellFormedness.of(
      "Cannot infer the name for a method with "+m.sig().ts().size()+" parameters.\n"
    + "Many"+(abs?" abstract":"")+" methods with "+m.sig().ts().size()+" parameters could be selected:\n"
    + Join.of(
        options.stream().map(mi->Message.displayString(mi.rc().get()+" "+mi.m().get().s())),
        "Candidates: ",", ",".\n")
    ).addSpan(m.sig().span().inner).addFrame(err.expRepr(origin), origin.span().inner);
  }
  public FearlessException ambiguousImplementationFor(List<M.Sig> ss, List<TName> options, Agreement at, FreshPrefix fresh){
    return Code.WellFormedness.of(    
      "Ambiguous implementation for method "+Message.displayString(at.mName().s())+" with "+at.mName().arity()+" parameters.\n"
    + "Different options are present in the implemented types:\n"
    + Join.of(
        options.stream().map(mi->Err.disp(err.tNameDirect(mi))),
        "Candidates: ",", ",".\n")
    + Err.up(err.expRepr(at.lit()))+" must declare a method "+Message.displayString(at.mName().s())+" explicitly implementing the desired behaviour.\n"
      ).addFrame(err.expRepr(at.lit()), at.span());
  }
  public FearlessException multipleWidenTo(E.Literal owner, List<IT.C> widen){
    var msg= new StringBuilder()
      .append(err.expRepr(owner))
      .append(" implements \"base.WidenTo[_]\" more than once.\n")
      .append("At most one \"base.WidenTo[_]\" supertype is allowed, ")
      .append("because it defines the preferred widened type.\n")
      .append(Join.of(
        widen.stream().map(c -> "  - " + Message.displayString(c.toString())),
        "Found the following base.WidenTo supertypes:\n","\n",""));
    return Code.WellFormedness.of(msg.toString())
      .addFrame(err.expRepr(owner),owner.span().inner);
  }
  public FearlessException extendedSealed(E.Literal owner,FreshPrefix fresh, TName isSealed){
    String ownerPkg= owner.name().pkgName();
    String sealedPkg= isSealed.pkgName();
    assert !ownerPkg.equals(sealedPkg);
    //is this failing, even if it uses Fresh and all?
    String ctx=Err.up(err.expRepr(owner));
    var msg= new StringBuilder()
      .append(ctx)
      .append(" implements sealed type ")
      .append(err.typeDecNamePkg(isSealed))
      .append(".\nSealed types can only be implemented in their own package.\n")
      .append(ctx)      
      .append(" is defined in package ")
      .append(Message.displayString(ownerPkg))
      .append(".\nType ")
      .append(Message.displayString(isSealed.simpleName()))
      .append(" is defined in package ")
      .append(Message.displayString(sealedPkg))
      .append(".\n");
    return Code.WellFormedness.of(msg.toString())
      .addFrame(err.expRepr(owner),owner.span().inner);
  }
}