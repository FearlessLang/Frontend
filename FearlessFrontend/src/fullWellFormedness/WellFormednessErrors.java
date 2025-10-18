package fullWellFormedness;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.X;
import fearlessFullGrammar.TName;
import fearlessParser.Parser;
import fearlessParser.RC;
import message.Code;
import message.FearlessException;
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
       ).addSpan(Parser.span(n.pos(),n.s().length()));
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
       ).addSpan(at);     
   }
   return Code.WellFormedness.of(
     "Undeclared name: name "+Message.displayString(tn.s())+" is not declared in package "+p.name()+".\n"
     ).addSpan(at);
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
     ).addSpan(Parser.span(n.pos(),n.name().length()));
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
      ).addSpan(Parser.span(name.pos(),name.s().length()));
  }
}