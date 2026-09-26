package message;

import java.util.Map;

import core.LiteralDeclarations;
import core.TName;

public record TypeNamePrinter(boolean trunc,String mainPkg, Map<String,String> uses){
  public TypeNamePrinter{ assert !mainPkg.isEmpty(); }
  public String of(TName n){ return trunc?trunc(pretty(n.s())):pretty(n.s()); }
  public String ofFull(TName n){ return pretty(n.s()); }
  private String pretty(String s){ return uses.getOrDefault(s,dropMainPkg(dropBaseForLit(s))); }
  private String dropMainPkg(String s){
    String pre= mainPkg + '.';
    return s.startsWith(pre) ? s.substring(pre.length()) : s;
  }
  private static String dropBaseForLit(String s){
    if (!s.startsWith("base.")){ return s; }
    String r= s.substring(5);
    if (r.isEmpty()){ return s; }
    if (!LiteralDeclarations.isPrimitiveLiteral(r)){ return s; }
    int d= r.length();
    if (d <= 15){ return r; }
    return r.substring(0,5)+"-"+r.substring(d-5);
  }
  private static String trunc(String s){
    int dot= s.lastIndexOf('.');
    if (dot == -1){ return truncSimple(s); }
    return "-."+truncSimple(s.substring(dot+1));
  }
  private static String truncSimple(String s){
    int l= s.length();
    if (l <= 9){ return s; }
    return s.substring(0, 3)+'-'+s.substring(l - 3);
  }
}