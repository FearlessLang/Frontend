package inject;

import java.util.ArrayList;
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

public final class ToInference{
  private static FearlessException undeclaredType(Methods meths, TName written, TName resolved){
    var p= meths.p();
    var declared= p.names().decNames();
    var all= Stream.concat(declared.stream().map(t -> t.withPkgName(p.name())), meths.other().dom().stream()).toList();
    var imported= p.map().entrySet().stream()
      .filter(e -> TokenKind.isKind(e.getKey(), TokenKind.UppercaseId))
      .flatMap(e -> all.stream()
        .filter(t -> t.s().equals(e.getValue()))
        .map(t -> new TName(p.name()+"."+e.getKey(), t.arity(), t.pos()))
      ).toList();
    var scope= Stream.concat(declared.stream(), imported.stream()).toList();
    return p.err().usedUndeclaredName(written, resolved, scope, all, WellFormednessErrors.resolution(p, written.s()));
  }
  private static TName resolve(Methods meths, TName tn){
    var p= meths.p();
    var pN= tn.pkgName();
    if (pN.isEmpty() && LiteralDeclarations.isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
    var s= pN.isEmpty() ? p.map().getOrDefault(tn.s(), p.name()+"."+tn.s()) : p.map().getOrDefault(pN, pN)+"."+tn.simpleName();
    var full= new TName(s, tn.arity(), tn.pos());
    var current= full.pkgName().equals(p.name());
    assert p.names().decNames().stream().allMatch(n -> n.pkgName().isEmpty());
    var defined= current ? p.names().decNames().contains(full.withoutPkgName()) : meths.other().__of(full) != null; //this also checks arity
    if (defined){ return full; } //here, we know it is not defined (either at all or with the right arity)
    throw undeclaredType(meths, tn, current && pN.isEmpty() ? full.withoutPkgName() : full);
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
