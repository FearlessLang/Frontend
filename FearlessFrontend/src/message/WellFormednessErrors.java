package message;

import java.net.URI;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import fullWellFormedness.Package;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.X;
import fearlessFullGrammar.TName;
import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import fullWellFormedness.Methods.Agreement;
import inferenceGrammar.B;
import inferenceGrammar.Declaration;
import inferenceGrammar.M;
import inferenceGrammarB.M.Sig;
import metaParser.Message;
import utils.Bug;

public final class WellFormednessErrors {
  private WellFormednessErrors(){}

  public static FearlessException notClean(URI uri, FileFull f){    
    return Code.WellFormedness.of(() -> buildMessageNotClean(uri,f));
  }
  private static String buildMessageNotClean(URI uri, FileFull f){
   String file= lastSegment(uri);
   List<String> bullets= new ArrayList<>();
   if (!f.maps().isEmpty()){ bullets.add("maps: " + previewList(f.maps(), 5)); }
   if (!f.uses().isEmpty()){ bullets.add("uses: " + previewList(f.uses(), 8)); }
   if (!f.role().isEmpty()){ bullets.add("role: " + f.role().get()+"\n"); }
   StringBuilder sb= new StringBuilder()
     .append("File is not the package head, but contains package head directives: ")
     .append(file)
     .append('\n')
     .append("Expected empty sections: maps, uses, role.\n");
   if (!bullets.isEmpty()){
     sb.append("Found non-empty:\n");
     bullets.forEach(b->sb.append("  - ").append(b).append('\n'));
   }
   sb.append("URI: ").append(uri);
   return sb.toString();
 }
 private static String previewList(List<?> c, int limit){
   StringBuilder sb = new StringBuilder();
   sb.append('[');
   int i = 0;
   for (var x : c){
     if (i > 0) sb.append(", ");
     if (i == limit){ sb.append("..."); break; }
     sb.append(String.valueOf(x));
     i++;
   }
   sb.append("] (size=").append(c.size()).append(')');
   return sb.toString();
 }
  public static FearlessException expectedSingleUriForPackage(List<URI> heads, String pkgName){
    return Code.WellFormedness.of(() -> buildMessageSingleUriForPackage(heads, pkgName));
  }
  private static String buildMessageSingleUriForPackage(List<URI> heads, String pkgName){
    if (heads.isEmpty()){
      return "No file named after package '" + pkgName + "'.\n"
        + "Expected exactly one URI whose last path segment is '"
        + pkgName + ".<ext>'.";
    }
    StringBuilder sb= new StringBuilder();
    sb.append("Ambiguous files for package '")
      .append(pkgName)
      .append("'.\n")
      .append("Found ")
      .append(heads.size())
      .append(" candidates:\n");
    heads.forEach(u->sb
      .append("  - ")
      .append(u)
      .append("  (name=")
      .append(lastSegment(u))
      .append(", base=")
      .append(baseName(lastSegment(u)))
      .append(", ext=")
      .append(extension(lastSegment(u)))
      .append(")\n"));
   sb.append("Rename or remove duplicates so only one file has basename '")
     .append(pkgName)
     .append("'.");
   return sb.toString();
  }
  private static String lastSegment(URI u){
    String p= u.getPath();
    int i= p.lastIndexOf('/');
    return i >= 0 ? p.substring(i + 1) : p;
  }
  private static String baseName(String name){
    int j= name.lastIndexOf('.');
    return j >= 0 ? name.substring(0, j) : name;
  }
  private static String extension(String name){
    int j= name.lastIndexOf('.');
    return j >= 0 && j + 1 < name.length() ? name.substring(j + 1) : "";
  }
 public static FearlessException noRole(URI uri, FileFull f){
   return Code.WellFormedness.of(() -> buildMessageNoRole(uri, f));
 }
 private static String buildMessageNoRole(URI uri, FileFull f){
   String file= lastSegment(uri);
   return new StringBuilder()
     .append("Missing role in head file: ")
     .append(file)
     .append('\n')
     .append("A top-level 'role' declaration is required in the package head file.\n")
     .append("URI: ")
     .append(uri)
     .toString();
   }

 public static FearlessException usedDeclaredNameClash(String pkgName, Set<TName> names, Set<String> keySet){
   for(TName n:names){ 
     var clash= keySet.contains(n.s());
     if (!clash){ continue; }
     return Code.WellFormedness.of(
       "Name clash: name "+Message.displayString(n.s())+" is declared in package "+pkgName+".\n"
       +"Name "+Message.displayString(n.s())+" is also used in a \"use\" directive.\n"
       ).addFrame("a type name",Parser.span(n.pos(),n.s().length()));
   }
   throw Bug.unreachable();
 }
 public static FearlessException usedUndeclaredName(TName tn, Package p){
   var at= Parser.span(tn.pos(),tn.s().length());
   var definedWithOtherArity= p.names().decNames().stream().allMatch(tni->tni.s().equals(tn.s()));
   if (definedWithOtherArity){
     return Code.WellFormedness.of(
       "Name: "+Message.displayString(tn.s())+" is not declared with arity "+tn.arity()+" in package "+p.name()+".\n"
     + "Did you accidentally add/omit a generic type parameter?\n"
       ).addFrame("a type name",at);
   }
   return Code.WellFormedness.of(
     "Undeclared name: name "+Message.displayString(tn.s())+" is not declared in package "+p.name()+".\n"
     ).addFrame("a type name",at);
   }
  public static FearlessException unkownUseHead(TName tn){
   var at= Parser.span(tn.pos(),tn.s().length());
   return Code.WellFormedness.of(
     "\"use\" directive referes to undeclared name: name "+Message.displayString(tn.simpleName())+" is not declared in package "+tn.pkgName()+".\n"
     ).addFrame("package header",at);
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
     "Gemeric type parameter "+Message.displayString(n.name())+" declared in package "+pkgName+".\n"
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
  public static FearlessException circularImplements(Map<TName, Declaration> rem){
    TName name = findCycleNode(rem);
    return Code.WellFormedness.of(
      "Circular implementation relation found involving "+Message.displayString(name.s())+".\n"
      ).addFrame("type declarations",Parser.span(name.pos(),name.s().length()));
  }
  private static TName findCycleNode(Map<TName,Declaration> rem){
    var color= new HashMap<TName,Integer>(rem.size());
    for (var k : rem.keySet()){
      var hit= dfs(rem,k,color);
      if (hit != null){ return hit; }
    }
    throw Bug.unreachable();
  }
  private static TName dfs(Map<TName,Declaration> rem,TName u,Map<TName,Integer> color){
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
      "Can not infer signature of method "+formatSig(m.sig())+".\n"
    + "No supertype has a method with "+m.sig().ts().size()+" parameters.\n"
      ).addSpan(Parser.span(m.sig().pos(),100));
  }
  private static String formatSig(M.Sig s){
    String res= s.toString().replace("[?]","").replace(" ("," <no_name>(");
    res= res.substring(1);    
    if (res.startsWith("? ")){ res= res.substring(2); }
    if (res.endsWith(";")){ res= res.substring(0,res.length()-1); }
    return Message.displayString(res);
  }
  public static FearlessException agreement(Agreement at, List<?> res, String msg){
    return agreement(at,Code.WellFormedness.of(
      msg+ " for method "+Message.displayString(at.mName().s())+" with "+at.mName().arity()+" parameters.\n"
    + "Different options are present in the implemented types: "+res.stream().map(o->Message.displayString(o.toString())).collect(Collectors.joining(", "))+".\n"
    + "Type "+Message.displayString(at.cName().s())+" must declare a method "+Message.displayString(at.mName().s())+" explicitly chosing the desired option.\n"
      ));
  }
  public static FearlessException agreementSize(Agreement at, List<List<B>> res) {
    return agreement(at,Code.WellFormedness.of(
      "Number of generic type parameters disagreement for method "+Message.displayString(at.mName().s())+" with "+at.mName().arity()+" parameters.\n"
    + "Different options are present in the implemented types: "+res.stream().map(o->Message.displayString(o.toString())).collect(Collectors.joining(", "))+".\n"
    + "Type "+Message.displayString(at.cName().s())+" must declare a method "+Message.displayString(at.mName().s())+" explicitly chosing the desired option.\n"
      ));
   }
  public static FearlessException ambiguosImpl(TName origin,boolean abs, M m, List<inferenceGrammarB.M.Sig> options){
    return agreement(origin,m.sig().pos(),Code.WellFormedness.of(
      "Can not infer the name for method with "+m.sig().ts().size()+" parameters.\n"
    + "Many"+(abs?" abstract":"")+" methods with "+m.sig().ts().size()+" parameters could be selected:\n"
    + "Candidates: "+options.stream()
        .map(mi->Message.displayString(mi.rc()+" "+mi.m().s()))
        .collect(Collectors.joining(", "))+".\n"
      ));
  }
  public static FearlessException ambiguousImplementationFor(List<Sig> ss, List<TName> options, Agreement at){
    return agreement(at,Code.WellFormedness.of(
      "Ambiguos implementation for method "+Message.displayString(at.mName().s())+" with "+at.mName().arity()+" parameters.\n"
    + "Different options are present in the implemented types:\n"
    + "Candidates: "+options.stream()
        .map(mi->Message.displayString(mi.s()))
        .collect(Collectors.joining(", "))+".\n"
    + "Type "+Message.displayString(at.cName().s())+" must declare a method "+Message.displayString(at.mName().s())+" explicitly implementing the desired behaviour.\n"
      ));
  }
  public static FearlessException noRetNoInference(TName origin, M m){
    return agreement(origin,m.sig().pos(),Code.WellFormedness.of(
      "Can not infer return type of method "+formatSig(m.sig())+".\n"
    + "No supertype has a method named "+Message.displayString(m.sig().m().get().s())+" with "+m.sig().ts().size()+" parameters.\n"
      ));
  }
  private static FearlessException agreement(Agreement at,FearlessException err){ return agreement(at.cName(),at.pos(),err); }
  private static FearlessException agreement(TName origin, Pos pos,FearlessException err){
    return err.addFrame("type declaration "+Message.displayString(origin.simpleName()),Parser.span(pos,100));
  }
}