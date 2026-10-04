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
  private ToInference(){}
  private static TName fCurrent(Methods meths, TName written, TName full){
    var p= meths.p();
    var simple= full.withoutPkgName();
    assert p.names().decNames().stream().allMatch(n->n.pkgName().isEmpty());
    var defined= p.names().decNames().contains(simple); //this also checks arity
    if (defined){ return full; } //here, we know it is not defined (either at all or with the right arity)
    throw undeclaredType(meths,written,written.pkgName().isEmpty()?simple:full);
  }
  private static FearlessException undeclaredType(Methods meths, TName written, TName resolved){
    var p= meths.p();
    var declared= p.names().decNames();
    var all= Stream.concat(declared.stream().map(t->t.withPkgName(p.name())), meths.other().dom().stream()).toList();
    var imported= p.map().entrySet().stream()
      .filter(e->TokenKind.isKind(e.getKey(), TokenKind.UppercaseId))
      .flatMap(e->all.stream()
        .filter(t->t.s().equals(e.getValue()))
        .map(t->new TName(p.name()+"."+e.getKey(), t.arity(),t.pos()))
      ).toList();
    var scope= Stream.concat(declared.stream(), imported.stream()).toList();
    return p.err().usedUndeclaredName(written, resolved, scope, all, WellFormednessErrors.resolution(p, written.s()));
  }
  private static TName resolve(Methods meths, TName tn){
    var p= meths.p();
    var pN= tn.pkgName();
    if (pN.isEmpty()){ return resolveSimple(meths,tn); }
    var pkg= p.map().getOrDefault(pN,pN);
    var full= tn.withOverridePkgName(pkg);
    if (pkg.equals(p.name())){ return fCurrent(meths,tn,full); }
    var lit= pkg.equals("base") && LiteralDeclarations.isPrimitiveLiteral(full.simpleName());
    if (lit){ return full; }
    if (meths.other().__of(full) != null){ return full; }
    throw undeclaredType(meths,tn,full);
  }
  private static TName resolveSimple(Methods meths, TName tn){
    var p= meths.p();
    if (LiteralDeclarations.isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
    var mapped= p.map().get(tn.s());
    if (mapped == null){ return fCurrent(meths,tn,tn.withPkgName(p.name())); }
    var res= new TName(mapped,tn.arity(),tn.pos());
    var current= res.pkgName().equals(p.name());
    var ok= current ? p.names().decNames().contains(res.withoutPkgName()) : meths.other().dom().contains(res);
    if (!ok){ throw undeclaredType(meths,tn,res); }
    return res;
  }
  public static List<E.Literal> of(Methods meths){
    Function<TName,TName> f= tn->resolve(meths,tn);
    var decs= new ArrayList<E.Literal>();
    for (var di : meths.p().decs()){
      var name= f.apply(di.name());
      new InjectionToInferenceVisitor(meths,name,new ArrayList<>(),f,decs).addDeclaration(name,RC.mut,di,true);
    }
    return List.copyOf(decs);
  }
}
