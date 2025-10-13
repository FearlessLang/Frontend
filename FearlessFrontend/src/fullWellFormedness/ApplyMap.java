package fullWellFormedness;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

import utils.Bug;

import fearlessFullGrammar.EVisitor;
import fearlessFullGrammar.M;
import fearlessFullGrammar.Parameter;
import fearlessFullGrammar.Sig;
import fearlessFullGrammar.TVisitor;
import fearlessFullGrammar.XPat;
import fearlessFullGrammar.B;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.E;
import fearlessFullGrammar.E.*;
import fearlessFullGrammar.T;
import fearlessFullGrammar.T.C;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.XPat.Destruct;
import fearlessFullGrammar.XPat.Name;

record TargetIn(String target, String in){}
public class ApplyMap {
  Package applyMap(Package p, Map<TargetIn,String> map){
    throw Bug.todo();    
  }
}
record ApplyMapVisitor(Function<String,String> f) implements EVisitor<E>,TVisitor<T>{
  @Override public T visitTX(T.X x){ return x; }
  @Override public T visitRCX(T.RCX x){ return x; }
  @Override public T visitReadImmX(T.ReadImmX x){ return x; }
  @Override public T visitRCC(T.RCC c){
    var ts= c.c().ts();
    var tName= c.c().name().s();
    var tStr= c.c().name().asUStrLit();
    var arity= c.c().name().arity();
    var tNameMap= new TName(f.apply(tName),arity,tStr);
    return new T.RCC(c.rc(),new C(tNameMap,ts.map(this::map)));
    }
  List<T> map(List<T> ts){ return ts.stream().map(t->t.accept(this)).toList(); }
  
  @Override public E visitX(X x){ return x; }
  @Override public E visitRound(Round r){ return new Round(r.e().accept(this)); }
  @Override public E visitImplicit(Implicit n){  return n;  }
  @Override public E visitTypedLiteral(TypedLiteral t){  return null; }
  @Override public T.RCC visitInnerRCC(T.RCC t){   return t; }
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