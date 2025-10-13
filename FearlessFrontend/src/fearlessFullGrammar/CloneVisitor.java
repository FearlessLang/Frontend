package fearlessFullGrammar;

import fearlessFullGrammar.E.*;
import fearlessFullGrammar.T.*;
import fearlessFullGrammar.XPat.Destruct;
import fearlessFullGrammar.XPat.Name;

public class CloneVisitor implements EVisitor<E>,TVisitor<T>,XPatVisitor<XPat>{
  @Override public XPat visitXPatName(Name n){   return null;  }
  @Override public XPat visitXPatDestruct(Destruct d){    return null; }
  
  @Override public T visitTX(T.X x){ return null; }
  @Override public T visitRCX(RCX x){ return null; }
  @Override public T visitReadImmX(ReadImmX x){ return null; }
  @Override public T visitRCC(RCC c){  return null; }
  
  @Override public E visitX(E.X n){ return null; }
  @Override public E visitRound(Round r){ return null; }
  @Override public E visitImplicit(Implicit n){  return null;  }
  @Override public E visitTypedLiteral(TypedLiteral t){  return null; }
  @Override public RCC visitInnerRCC(RCC t){   return null; }
  @Override public E visitDeclarationLiteral(DeclarationLiteral c){    return null;  }
  @Override public E visitLiteral(Literal c){    return null;  }
  @Override public E visitCall(Call c){    return null;  }
  @Override public CallSquare visitInnerCallSquare(CallSquare c){  return null; }
  @Override public E visitStringInter(StringInter i){   return null; }
  @Override public XPat visitInnerXPat(XPat x){  return null; }
  @Override public M visitInnerM(M m){  return null; }
  @Override public Sig visitInnerSig(Sig s){ return null; }
  @Override public Parameter visitInnerParameter(Parameter p){   return null; }
  @Override public B visitInnerB(B b){  return null; }
  @Override public Literal visitInnerLiteral(Literal l){   return null; }
  @Override public Declaration visitInnerDeclaration(Declaration d){    return null; }
}