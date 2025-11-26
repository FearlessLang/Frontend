package message;

import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import core.B;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.X;
import fearlessFullGrammar.TName;
import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
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

public final class WellFormednessErrors {
  private WellFormednessErrors(){}

  public static FearlessException notClean(URI uri, FileFull f){
    return Code.WellFormedness.of(() -> buildMessageNotClean(f))
      .addSpan(new Span(uri,0,0,1,1));
  }
  private static String buildMessageNotClean(FileFull f){
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
  private static String previewList(List<?> c, int limit){
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
  
  public static FearlessException expectedSingleUriForPackage(List<URI> heads, String pkgName){
    return Code.WellFormedness.of(() -> buildMessageSingleUriForPackage(heads, pkgName));
  }
  private static String buildMessageSingleUriForPackage(List<URI> heads, String pkgName){
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
  public static FearlessException noRole(URI uri, FileFull f){
    return Code.WellFormedness.of(() -> buildMessageNoRole(uri, f)).addSpan(new Span(uri,0,0,1,1));
  }
  private static String buildMessageNoRole(URI uri, FileFull f){
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
  public static FearlessException usedDeclaredNameClash(String pkgName, Set<TName> names, Set<String> keySet){
    for(TName n:names){ 
      var clash= keySet.contains(n.s());
      if (!clash){ continue; }
      return Code.WellFormedness.of(
        "Name clash: name "+Message.displayString(n.s())+" is declared in package "+Message.displayString(pkgName)+".\n"
        +"Name "+Message.displayString(n.s())+" is also used in a \"use\" directive.\n"
        ).addFrame("a type name",Parser.span(n.pos(),n.s().length()));
    }
    throw Bug.unreachable();
  }
  public static FearlessException usedUndeclaredName(TName tn, String contextPkg, List<TName> scope, List<TName> all){
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
      if(typedPkg.isEmpty()){ return Optional.empty(); }
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
          msg.append("Visible packages: ")
            .append(cs.stream().map(Message::displayString).collect(Collectors.joining(", ")))
            .append(".\n");
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
        .append(" generic parameter(s) in package ")
        .append(Message.displayString(targetPkg))
        .append(".\n")
        .append("Name ")
        .append(Message.displayString(typedSimple))
        .append(" is only declared with ");
      if (arities.size() == 1){ msg.append(arities.getFirst()).append(" generic parameter(s)"); }
      else{msg
        .append("the following numbers of generic parameters: ")
        .append(arities.stream().map(Object::toString).collect(Collectors.joining(", ")));
      }
      msg.append(".\nDid you accidentally add or omit a generic type parameter?\n");
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
      msg.append("Did you mean ")
        .append(ss.stream().map(Message::displayString).collect(Collectors.joining(" or ")))
        .append(" ?\n")
        .append(addUse);
    }    
    private static String addUse="Add a \"use\" or write the fully qualified name.\n";
    private FearlessException make(StringBuilder msg){
      trimTrailingNewline(msg);
      return Code.WellFormedness.of(msg.toString()).addFrame("a type name", at()); }
    private Span at(){ return Parser.span(tn.pos(), tn.s().length()); }
  }
  private static void trimTrailingNewline(StringBuilder sb){
    int len= sb.length();
    if (len > 0 && sb.charAt(len - 1) == '\n'){ sb.setLength(len - 1); }
  }
  public static FearlessException unknownUseHead(TName tn){
    var at= Parser.span(tn.pos(),tn.s().length());
    return Code.WellFormedness.of(
      "\"use\" directive refers to undeclared name: type "
      +Message.displayString(tn.simpleName())
      +" is not declared in package " + Message.displayString(tn.pkgName()) + ".\n"
    ).addFrame("package header", at);
  }
 public static FearlessException genericTypeVariableShadowTName(String pkgName, Map<TName, Set<X>> allXs, List<String> allNames, Set<String> use){
   var mergeAllXs= allXs.values().stream().flatMap(Set::stream).toList();
   for(var n : mergeAllXs){
     var clashDec= allNames.contains(n.name());
     var clashUse= use.contains(n.name());
     if (clashDec || clashUse){ return shadowMsg(pkgName,n,clashUse); }
   }
   throw Bug.unreachable();
 }
 private static FearlessException shadowMsg(String pkgName, T.X n, boolean use){
   return Code.WellFormedness.of(
     "Generic type parameter " + Message.displayString(n.name())
     +" is declared in package \"" + pkgName + "\".\n"
     + "Name "+Message.displayString(n.name())+" is also used "
     + (use?"in a \"use\" directive.\n":"as a type name.\n")
     ).addFrame("a type name",Parser.span(n.pos(),n.name().length()));
  }

 public static FearlessException duplicatedBound(List<RC> es, T.X n){
   var dup= es.stream()
     .filter(e->es.stream().filter(ei->ei.equals(e)).count()>1)
     .findFirst().get();
   return Code.WellFormedness.of(
       "Duplicate reference capability in the generic type parameter "+Message.displayString(n.name())+".\n"
       + "Reference capability "+Message.displayString(dup.name())+" is repeated.\n"
       ).addSpan(Parser.span(n.pos(),n.name().length()));
    }
  public static FearlessException duplicatedName(TName name) {
    return Code.WellFormedness.of(
      "Duplicate type declaration for "+Message.displayString(name.s())+".\n"
      ).addFrame("a type name",Parser.span(name.pos(),name.s().length()));
  }
  public static FearlessException circularImplements(Map<TName,E.Literal> rem){
    TName name = findCycleNode(rem);
    return Code.WellFormedness.of(
      "Circular implementation relation found involving "+Message.displayString(name.s())+".\n"
      ).addFrame("type declarations",Parser.span(name.pos(),name.s().length()));
  }
  private static TName findCycleNode(Map<TName,E.Literal> rem){
    var color= new HashMap<TName,Integer>(rem.size());
    for (var k : rem.keySet()){
      var hit= dfs(rem,k,color);
      if (hit != null){ return hit; }
    }
    throw Bug.unreachable();
  }
  private static TName dfs(Map<TName,E.Literal> rem,TName u,Map<TName,Integer> color){
    Integer cu= color.get(u);
    if (cu != null){ return cu == 1 ? u : null; }
    color.put(u,1);
    for(var c:rem.get(u).cs()){
      if(!rem.containsKey(c.name())){ continue; }
      var hit= dfs(rem,c.name(),color);
      if (hit != null){ return hit; }
    }
    color.put(u,2);
    return null;
  }
  public static FearlessException noSourceToInferFrom(M m){
    return Code.WellFormedness.of(//Note: an 'origin' is likely to be a fresh name anyway
      "Cannot infer signature of method "+formatSig(m.sig())+".\n"
    + "No supertype has a method with "+m.sig().ts().size()+" parameters.\n"
      ).addSpan(Parser.span(m.sig().pos(),100));
  }
  private static String formatSig(M.Sig s){
    String res= s.toString()
      .replace("[?]","")
      .replace(" ("," <no_name>(")
      .replace("@!","");
    res= res.substring(1);    
    if (res.startsWith("? ")){ res= res.substring(2); }
    if (res.endsWith(";")){ res= res.substring(0,res.length()-1); }
    return Message.displayString(res);
  }
  public static FearlessException agreement(Agreement at, FreshPrefix fresh, List<?> res, String msg){
    return agreement(at,fresh,Code.WellFormedness.of(
      msg+ " for method "+Message.displayString(at.mName().s())+" with "+at.mName().arity()+" parameters.\n"
    + "Different options are present in the implemented types: "+res.stream()
      .map(o->Message.displayString(o.toString())).collect(Collectors.joining(", "))+".\n"
    + "Type "+Message.displayString(at.cName().s())+" must declare a method "+Message.displayString(at.mName().s())+" explicitly choosing the desired option.\n"
      ));
  }
  public static FearlessException agreementSize(Agreement at, FreshPrefix fresh, List<List<B>> res) {
    return agreement(at,fresh,Code.WellFormedness.of(
    "The number of generic type parameters disagrees for method "
    + Message.displayString(at.mName().s())
    + " with " + at.mName().arity() + " parameters.\n"
    + "Different options are present in the implemented types: "
    + res.stream().map(o->Message.displayString(o.toString())).collect(Collectors.joining(", "))+".\n"
    + "Type "+Message.displayString(at.cName().s())
    + " cannot implement all of those types.\n"
      ));
   }
   public static FearlessException methodGenericArityDisagreesWithSupers(Agreement at, FreshPrefix fresh, int userArity, int superArity, List<B> userBs, List<B> superBs){
    return agreement(at,fresh,Code.WellFormedness.of(
      "Method " + Message.displayString(at.mName().s())
    + " declares " + userArity + " generic parameter(s), "
    + "but supertypes declare " + superArity + ".\n"
    + "Local declaration: " + Message.displayString(userBs.toString()) + ".\n"
    + "From supertypes: " + Message.displayString(superBs.toString()) + ".\n"
    + "Change the local number of generic parameters to "
    + superArity + ", or adjust the supertypes.\n" 
    ));
  }

  public static FearlessException ambiguousImpl(TName origin, FreshPrefix fresh, boolean abs, M m, List<inference.M.Sig> options){
    return agreement(origin,fresh,m.sig().pos(),Code.WellFormedness.of(
      "Cannot infer the name for method with "+m.sig().ts().size()+" parameters.\n"
    + "Many"+(abs?" abstract":"")+" methods with "+m.sig().ts().size()+" parameters could be selected:\n"
    + "Candidates: "+options.stream()
        .map(mi->Message.displayString(mi.rc().get()+" "+mi.m().get().s()))
        .collect(Collectors.joining(", "))+".\n"
      ));
  }
  public static FearlessException ambiguousImplementationFor(List<M.Sig> ss, List<TName> options, Agreement at, FreshPrefix fresh){
    return agreement(at,fresh,Code.WellFormedness.of(    
      "Ambiguous implementation for method "+Message.displayString(at.mName().s())+" with "+at.mName().arity()+" parameters.\n"
    + "Different options are present in the implemented types:\n"
    + "Candidates: "+options.stream()
        .map(mi->Message.displayString(mi.s()))
        .collect(Collectors.joining(", "))+".\n"
    + "Type "+Message.displayString(at.cName().s())+" must declare a method "+Message.displayString(at.mName().s())+" explicitly implementing the desired behaviour.\n"
      ));
  }
  public static FearlessException noRetNoInference(TName origin, M m, FreshPrefix fresh){
    return agreement(origin,fresh,m.sig().pos(),Code.WellFormedness.of(
      "Cannot infer return type of method "+formatSig(m.sig())+".\n"
    + "No supertype has a method named "+Message.displayString(m.sig().m().get().s())+" with "+m.sig().ts().size()+" parameters.\n"
      ));
  }
  public static FearlessException multipleWidenTo(TName owner, List<IT.C> widen){
    var msg= new StringBuilder()
      .append("Type ")
      .append(Message.displayString(owner.s()))
      .append(" implements base.WidenTo more than once.\n")
      .append("At most one base.WidenTo[T] supertype is allowed, ")
      .append("because it defines the preferred widened type.\n")
      .append("Found the following base.WidenTo supertypes:\n")
      .append(widen.stream()
        .map(c -> "  - " + Message.displayString(c.toString()))
        .collect(Collectors.joining("\n")));
    return Code.WellFormedness.of(msg.toString())
      .addSpan(Parser.span(owner.pos(), owner.simpleName().length()));
  }
  public static FearlessException extendedSealed(TName owner,FreshPrefix fresh, TName isSealed){
    String ownerPkg= owner.pkgName();
    String sealedPkg= isSealed.pkgName();
    assert !ownerPkg.equals(sealedPkg);
    String ctx= typeContextLabel("Type ","Literal implementing type ", owner,fresh);
    var msg= new StringBuilder()
      .append(ctx)
      .append(" implements sealed type ")
      .append(Message.displayString(isSealed.s()))
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
      .addFrame(typeContextLabel(owner, fresh),Parser.span(owner.pos(), owner.simpleName().length()));
  }
  private static FearlessException agreement(Agreement at, FreshPrefix fresh, FearlessException err){ return agreement(at.cName(), fresh, at.pos(), err); }
  private static FearlessException agreement(TName origin, FreshPrefix fresh, Pos pos, FearlessException err){
    return err.addFrame(typeContextLabel(origin, fresh), Parser.span(pos,100));
  }
  private static String typeContextLabel(String onT, String onLit,TName origin, FreshPrefix fresh){
    var base= fresh.anonSuperT(origin);
    if (base.isEmpty()){ return onT+Message.displayString(origin.simpleName()); }
    return onLit+Message.displayString(base.get().s());
  }
  private static String typeContextLabel(TName origin, FreshPrefix fresh){
    return typeContextLabel("type declaration ","literal implementing type ",origin,fresh);
  }
}