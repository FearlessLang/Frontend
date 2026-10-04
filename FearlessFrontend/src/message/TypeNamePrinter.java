package message;

import java.util.Map;
import java.util.function.Consumer;

import core.LiteralDeclarations;
import core.TName;

public record TypeNamePrinter(boolean trunc,String mainPkg, Map<String,String> uses, Consumer<String> printed){
  public TypeNamePrinter{ assert !mainPkg.isEmpty(); }
  public String of(TName n){ return trunc?trunc(ofFull(n)):ofFull(n); }
  public String ofFull(TName n){
    printed.accept(n.s());
    return uses.getOrDefault(n.s(),dropMainPkg(dropBaseForLit(n.s())));
  }
  private String dropMainPkg(String s){
    var pre= mainPkg + '.';
    return s.startsWith(pre) ? s.substring(pre.length()) : s;
  }
  private static String dropBaseForLit(String s){
    if (!s.startsWith("base.")){ return s; }
    var r= s.substring(5);
    if (r.isEmpty()){ return s; }
    if (!LiteralDeclarations.isPrimitiveLiteral(r)){ return s; }
    var d= r.length();
    if (d <= 15){ return r; }
    return r.substring(0,5)+"-"+r.substring(d-5);
  }
  private static String trunc(String s){
    var dot= TName.pkgDot(s);
    if (dot == -1){ return truncSimple(s); }
    return "-."+truncSimple(s.substring(dot+1));
  }
  private static String truncSimple(String s){
    var l= s.length();
    if (l <= 9){ return s; }
    return s.substring(0, 3)+'-'+s.substring(l - 3);
  }
}