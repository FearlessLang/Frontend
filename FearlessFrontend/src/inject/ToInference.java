package inject;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Stream;

import core.FearlessException;
import core.LiteralDeclarations;
import core.RC;
import core.TName;
import fearlessParser.TokenKind;
import inference.E;
import message.WellFormednessErrors;
import pkgmerge.Package;
import utils.OneOr;

public final class ToInference{
  private static FearlessException undeclaredType(Methods meths, TName written, TName resolved){
    var p= meths.p();
    var declared= p.names().decNames();
    var real= Stream.concat(declared.stream().map(t -> t.withPkgName(p.name())), meths.other().dom().stream()).toList();
    var imported= p.map().entrySet().stream()
      .filter(e -> TokenKind.isKind(e.getKey(), TokenKind.UppercaseId))
      .flatMap(e -> real.stream()
        .filter(t -> t.s().equals(e.getValue()))
        .map(t -> new TName(p.name()+"."+e.getKey(), t.arity(), t.pos()))
      ).toList();
    var scope= Stream.concat(declared.stream(), imported.stream()).toList();
    var all= real.stream().map(t -> written(p, t)).toList();
    return p.err().usedUndeclaredName(written, resolved, scope, all, meths.other().ranks(), WellFormednessErrors.resolution(p, written.s()));
  }
  private static TName written(Package p, TName t){
    return t.withoutPkgName().withPkgName(Package.writtenPkg(p.map(), t.pkgName()));
  }
  private static TName writtenOnce(Methods meths, TName tn, TName full){
    var p= meths.p();
    var pN= tn.pkgName();
    if (pN.isEmpty()){ return full; }
    if (pN.equals(p.name())){ throw p.err().typeOfTheCurrentPackageQualified(tn, sameSimpleName(meths, tn)); }
    OneOr.opt("aliases of "+full, p.uses().stream().filter(u -> full.s().equals(p.map().get(u.out())))).ifPresent(u -> { throw p.err().typeWithAnAlias(tn, u); });
    return full;
  }
  private static List<TName> sameSimpleName(Methods meths, TName tn){
    var p= meths.p();
    return meths.other().dom().stream()
      .filter(t -> t.simpleName().equals(tn.simpleName()) && !p.map().containsValue(t.s()))
      .sorted(Comparator.comparing(t -> written(p, t).s())).toList();
  }
  private static TName resolve(Methods meths, TName tn){
    var p= meths.p();
    var pN= tn.pkgName();
    if (pN.isEmpty() && LiteralDeclarations.isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
    if (p.map().containsValue(pN)){ throw p.err().typeOfAMapTarget(tn, Package.visible(p.map(), meths.other().dom())); }
    var s= pN.isEmpty() ? p.map().getOrDefault(tn.s(), p.name()+"."+tn.s()) : p.map().getOrDefault(pN, pN)+"."+tn.simpleName();
    var full= new TName(s, tn.arity(), tn.pos());
    var current= full.pkgName().equals(p.name());
    assert p.names().decNames().stream().allMatch(n -> n.pkgName().isEmpty());
    var defined= current ? p.names().decNames().contains(full.withoutPkgName()) : meths.other().__of(full) != null; //this also checks arity
    if (defined){ return writtenOnce(meths, tn, full); } //here, we know it is not defined (either at all or with the right arity)
    throw undeclaredType(meths, tn, current && pN.isEmpty() ? full.withoutPkgName() : written(p, full));
  }
  public static List<E.Literal> of(Methods meths){
    Function<TName,TName> f= tn -> resolve(meths, tn);
    var decs= new ArrayList<E.Literal>();
    for (var di : meths.p().decs()){
      var name= f.apply(di.name());
      new InjectionToInferenceVisitor(meths, name, new ArrayList<>(), f, decs).addDeclaration(name, RC.mut, di, true);
    }
    return List.copyOf(decs);
  }
}
