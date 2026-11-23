package message;

import java.util.Map;
import java.util.function.Consumer;

import core.LiteralDeclarations;
import core.TName;

public record TypeNamePrinter(String mainPkg, Map<String,String> uses, Consumer<String> printed){
  public TypeNamePrinter{ assert !mainPkg.isEmpty(); }
  public String of(TName n){
    var pkg= n.pkgName();
    var baseLit= pkg.equals("base") && LiteralDeclarations.isPrimitiveLiteral(n.simpleName());
    if (baseLit){ return n.simpleName(); }
    if (uses.containsKey(pkg)){ printed.accept(n.s()); }
    return uses.getOrDefault(n.s(), pkg.isEmpty() || pkg.equals(mainPkg) ? n.simpleName() : uses.getOrDefault(pkg, pkg)+"."+n.simpleName());
  }
}