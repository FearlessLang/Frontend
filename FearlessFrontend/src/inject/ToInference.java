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

public class ToInference{
  private TName fCurrent(Methods meths, TName full, boolean withPkg){
    var p= meths.p();
    var simple= full.withoutPkgName();
    assert p.names().decNames().stream().allMatch(n->n.pkgName().isEmpty());
    var defined= p.names().decNames().contains(simple); //this also checks arity
    if (defined){ return full; } //here, we know it is not defined (either at all or with the right arity)
    throw undeclaredType(withPkg?full:simple,p.name(),meths);
  }
  private FearlessException undeclaredType(TName tn, String contextPkg, Methods meths){
    var p= meths.p();
    var otherTypes= meths.other().dom();
    var declared= p.names().decNames();
    var imported= p.map().entrySet().stream()
      .filter(e->TokenKind.isKind(e.getKey(), TokenKind.UppercaseId))
      .flatMap(e->otherTypes.stream()
        .filter(t->t.s().equals(e.getValue()))
        .map(t->new TName(p.name()+"."+e.getKey(), t.arity(),t.pos()))
      ).toList();
    var scope= Stream.concat(declared.stream(), imported.stream()).toList();
    var all= Stream.concat(declared.stream().map(t->t.withPkgName(p.name())), otherTypes.stream()).toList();
    return p.err().usedUndeclaredName(tn, contextPkg, scope, all);
  }
  private TName resolve(Methods meths, TName tn){
    var p= meths.p();
    var pN= tn.pkgName();
    if (pN.isEmpty()){ return resolveSimple(meths,tn); }
    var pkg= p.map().getOrDefault(pN,pN);
    tn= tn.withOverridePkgName(pkg);
    if (pkg.equals(p.name())){ return fCurrent(meths,tn,true); }
    var lit= pkg.equals("base") && LiteralDeclarations.isPrimitiveLiteral(tn.simpleName());
    if (lit){ return tn; }
    if (meths.other().__of(tn) != null){ return tn; }
    throw undeclaredType(tn,p.name(),meths);
  }
  private TName resolveSimple(Methods meths, TName tn){
    var p= meths.p();
    if (LiteralDeclarations.isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
    var mapped= p.map().get(tn.s());
    if (mapped == null){ return fCurrent(meths,tn.withPkgName(p.name()),false); }
    var res= new TName(mapped,tn.arity(),tn.pos());
    var ok= meths.other().dom().contains(res);
    if (!ok){ throw undeclaredType(tn,res.pkgName(),meths); }
    return res;
  }
  public List<E.Literal> of(Methods meths){
    Function<TName,TName> f= tn->resolve(meths,tn);
    ArrayList<E.Literal> decs= new ArrayList<>();
    for (var di : meths.p().decs()){
      TName name= f.apply(di.name());
      new InjectionToInferenceVisitor(meths,name,new ArrayList<>(),f,decs).addDeclaration(name,RC.mut,di,true);
    }
    return List.copyOf(decs);
  }
}
