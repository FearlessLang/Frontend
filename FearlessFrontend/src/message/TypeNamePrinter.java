package message;

import java.util.Map;
import java.util.function.Consumer;

import core.LiteralDeclarations;
import core.TName;

public record TypeNamePrinter(String mainPkg, Map<String,String> uses, Consumer<String> printed){
  public TypeNamePrinter{ assert !mainPkg.isEmpty(); }
  public String of(TName n){
    var lit= dropBaseForLit(n.s());
    if (!lit.equals(n.s())){ return lit; }
    var pkg= n.pkgName();
    if (uses.containsKey(pkg)){ printed.accept(n.s()); }
    return uses.getOrDefault(n.s(), pkg.isEmpty() || pkg.equals(mainPkg) ? n.simpleName() : uses.getOrDefault(pkg, pkg)+"."+n.simpleName());
  }
  private static String dropBaseForLit(String s){
    if (!s.startsWith("base.")){ return s; }
    var r= s.substring(5);
    return LiteralDeclarations.isPrimitiveLiteral(r) ? r : s;
  }
}