package pkgmerge;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Supplier;

import fearlessFullGrammar.*;
import fearlessFullGrammar.E.*;
import message.WellFormednessErrors;
import java.util.Map;

public class AllDeclaredNames implements EVisitor<Void>{
  AllDeclaredNames(WellFormednessErrors err){this.err= err;}
  WellFormednessErrors err;
  Set<TName> decNames= new LinkedHashSet<>();
  Map<TName,Set<T.X>> Xs= new LinkedHashMap<>();
  Map<TName,Set<String>> xs= new LinkedHashMap<>();
  // lastTopNames: all parameter names and this-names appearing anywhere
  // in the current top Declaration (including nested DeclarationLiteral)
  LinkedHashSet<String> lastTopNames;
  // lastTopXs: all generic Bs appearing anywhere in the the current top Declaration
  LinkedHashSet<T.X> lastTopXs;
  public void visitTopDeclaration(Declaration d,String pkgName){
    lastTopNames= new LinkedHashSet<>();
    lastTopXs= new LinkedHashSet<>();
    visitInnerDeclaration(d);
    var n= d.name().withPkgName(pkgName);
    assert !xs.containsKey(n);
    assert !Xs.containsKey(n);
    xs.put(n, Collections.unmodifiableSet(lastTopNames));
    Xs.put(n, Collections.unmodifiableSet(lastTopXs));    
  }
  private B visitInnerB(B b){ lastTopXs.add(b.x()); return b; }
  private Parameter visitInnerParameter(Parameter p){ p.xp().ifPresent(this::visitInnerXPat); return p; }
  private XPat visitInnerXPat(XPat x){ x.parameterNames().forEach(lastTopNames::add); return x; }
  private Sig visitInnerSig(Sig s){
    s.bs().ifPresent(bs->bs.forEach(this::visitInnerB));
    s.parameters().forEach(this::visitInnerParameter);
    return s;
  }

  private Declaration visitInnerDeclaration(Declaration d){
    //Note: there is never any kind of shadowing allowed in fearless. Also, nested names do live in the top level scope
    if (!decNames.add(d.name())){ throw err.duplicatedName(d.name()); }
    d.bs().ifPresent(bs->bs.forEach(this::visitInnerB));
    d.l().accept(this);
    return d;
  }
  @Override public Void visitLiteral(Literal c){
    c.thisName().ifPresent(n->lastTopNames.add(n.name()));
    c.methods().forEach(this::visitInnerM);
    return null;
  }
  private M visitInnerM(M m){
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
}