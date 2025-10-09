package fullWellFormedness;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;

import fearlessFullGrammar.FileFull;
import message.Code;
import message.FearlessException;

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
}