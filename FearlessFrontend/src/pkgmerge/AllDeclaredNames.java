package pkgmerge;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;

import core.TName;
import fearlessFullGrammar.*;
import fearlessFullGrammar.E.*;
import message.WellFormednessErrors;

public class AllDeclaredNames{
  AllDeclaredNames(WellFormednessErrors err){ this.err= err; }
  WellFormednessErrors err;
  LinkedHashSet<TName> decNames= new LinkedHashSet<>();
  LinkedHashMap<TName,Set<T.X>> Xs= new LinkedHashMap<>();
  LinkedHashMap<TName,Set<String>> xs= new LinkedHashMap<>();
  // lastTopNames: all parameter names and this-names appearing anywhere
  // in the current top Declaration (including nested DeclarationLiteral)
  LinkedHashSet<String> lastTopNames;
  // lastTopXs: all generic Bs appearing anywhere in the the current top Declaration
  LinkedHashSet<T.X> lastTopXs;
  public void visitTopDeclaration(Declaration d){
    lastTopNames= new LinkedHashSet<>();
    lastTopXs= new LinkedHashSet<>();
    visitInnerDeclaration(d);
    var n= d.name().withPkgName(err.pkgName());
    assert !xs.containsKey(n);
    assert !Xs.containsKey(n);
    xs.put(n, Collections.unmodifiableSet(lastTopNames));
    Xs.put(n, Collections.unmodifiableSet(lastTopXs));
  }
  private void visitInnerB(B b){ lastTopXs.add(b.x()); }
  private void visitInnerParameter(Parameter p){ p.xp().ifPresent(this::visitInnerXPat); }
  private void visitInnerXPat(XPat x){ x.parameterNames().forEach(lastTopNames::add); }
  private void visitInnerSig(Sig s){
    s.bs().ifPresent(bs->bs.forEach(this::visitInnerB));
    s.parameters().forEach(this::visitInnerParameter);
  }
  private void visitInnerDeclaration(Declaration d){
    //Note: there is never any kind of shadowing allowed in fearless. Also, nested names do live in the top level scope
    if (!decNames.add(d.name())){ throw err.duplicatedName(d.name()); }
    d.bs().ifPresent(bs->bs.forEach(this::visitInnerB));
    visitLiteral(d.l());
  }
  private void visitLiteral(Literal c){
    c.thisName().ifPresent(n->lastTopNames.add(n.name()));
    c.methods().forEach(this::visitInnerM);
  }
  private void visitInnerM(M m){
    m.sig().ifPresent(this::visitInnerSig);
    m.body().ifPresent(this::visitE);
  }
  private void visitE(E e){
    switch (e){
      case X _, Implicit _ -> {}
      case Round r -> visitE(r.e());
      case TypedLiteral t -> t.l().ifPresent(this::visitLiteral);
      case DeclarationLiteral c -> visitInnerDeclaration(c.dec());
      case Literal c -> visitLiteral(c);
      case Call c -> visitCall(c);
    }
  }
  private void visitCall(Call c){
    visitE(c.e());
    c.pat().ifPresent(this::visitInnerXPat);
    c.es().forEach(this::visitE);
  }
}
