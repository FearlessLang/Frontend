package fullWellFormedness;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import fearlessFullGrammar.*;
import fearlessFullGrammar.E.*;
import message.WellFormednessErrors;

import java.util.Map;
import utils.Bug;
public class AllDeclaredNames implements EVisitor<Void>{
  Set<TName> decNames= new LinkedHashSet<>();
  Map<TName,Set<T.X>> Xs= new LinkedHashMap<>();
  Map<TName,Set<String>> xs= new LinkedHashMap<>();
  LinkedHashSet<String> lastTopNames;
  LinkedHashSet<T.X> lastTopXs;
  public void visitTopDeclaration(Declaration d,String pkgName){
    lastTopNames= new LinkedHashSet<>();
    lastTopXs= new LinkedHashSet<>();
    visitInnerDeclaration(d);
    assert !xs.containsKey(d.name());
    assert !Xs.containsKey(d.name());
    var n= d.name().withPkgName(pkgName);
    xs.put(n, Collections.unmodifiableSet(lastTopNames));
    Xs.put(n, Collections.unmodifiableSet(lastTopXs));
    
  }
  @Override public B visitInnerB(B b){ lastTopXs.add(b.x()); return b; }
  @Override public Parameter visitInnerParameter(Parameter p){ p.xp().ifPresent(this::visitInnerXPat); return p; }
  @Override public XPat visitInnerXPat(XPat x){ x.parameterNames().forEach(lastTopNames::add); return x; }
  @Override public Sig visitInnerSig(Sig s){ s.parameters().forEach(this::visitInnerParameter); return s; }

  @Override public Declaration visitInnerDeclaration(Declaration d){
    if (!decNames.add(d.name())){ throw WellFormednessErrors.duplicatedName(d.name()); }
    d.bs().ifPresent(bs->bs.forEach(this::visitInnerB));
    d.l().accept(this);
    return d;
  }
  @Override public Void visitLiteral(Literal c){
    c.thisName().ifPresent(n->lastTopNames.add(n.name()));
    c.methods().forEach(this::visitInnerM);
    return null;
  }
  @Override public M visitInnerM(M m){
    m.sig().ifPresent(this::visitInnerSig);
    m.body().ifPresent(e->e.accept(this));
    return m;
  }
  @Override public Void visitX(X n){ return null; }
  @Override public Void visitRound(Round r){ return r.e().accept(this); }
  @Override public Void visitImplicit(Implicit n){ return null; }
  @Override public Void visitTypedLiteral(TypedLiteral t){
    t.l().ifPresent(this::visitLiteral);
    return null;
  }
  @Override public Void visitDeclarationLiteral(DeclarationLiteral c){
    this.visitInnerDeclaration(c.dec());    
    return null;
  }
  @Override public Void visitCall(Call c){
    c.e().accept(this);
    c.es().forEach(ei->ei.accept(this));
    return null;
  }
  @Override public Void visitStringInter(StringInter i){
    i.e().ifPresent(e->e.accept(this));
    i.es().forEach(e->e.accept(this));
    return null;
  }
  @Override public CallSquare visitInnerCallSquare(CallSquare c){ throw Bug.unreachable(); }
  @Override public Literal visitInnerLiteral(Literal l){ throw Bug.unreachable(); }
  @Override public T.RCC visitInnerRCC(T.RCC t){ throw Bug.unreachable(); }
}