package message;

import java.util.Map;
import fearlessFullGrammar.TName;
import optimizedTypes.LiteralDeclarations;

public record TypeNamePrinter(String mainPkg, Map<String,String> uses){
  public TypeNamePrinter{ assert !mainPkg.isEmpty(); }
  public String of(TName n){ return trunc(pretty(n.s())); }
  private String pretty(String s){
    String a= uses.get(s);
    if (a != null){ return a; }
    s = dropBaseForLit(s);
    s = dropMainPkg(s);
    return s;
  }
  private String dropMainPkg(String s){
    if (mainPkg.isEmpty()){ return s; }
    String pre= mainPkg + '.';
    return s.startsWith(pre) ? s.substring(pre.length()) : s;
  }
  private static String dropBaseForLit(String s){
    if (!s.startsWith("base.")){ return s; }
    String r= s.substring(5);
    if (r.isEmpty()){ return s; }
    if (!LiteralDeclarations.isPrimitiveLiteral(r)){ return s; }
    if (r.length() <= 5){ return r; }
    char ch= r.charAt(0);
    if (ch == '"'){ return "\"-\""; }
    if (ch == '`'){ return "`-`"; }
    return r;
  }
  private static String trunc(String s){
    int dot= s.lastIndexOf('.');
    if (dot < 0){ return truncSimple(s); }
    return "-."+truncSimple(s.substring(dot+1));
  }
  private static String truncSimple(String s){
    int l= s.length();
    if (l <= 9){ return s; }
    return s.substring(0, 3)+'-'+s.substring(l - 3, l);
  }
}