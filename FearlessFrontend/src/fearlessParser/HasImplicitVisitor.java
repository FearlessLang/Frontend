package fearlessParser;

import fearlessFullGrammar.B;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.E.Call;
import fearlessFullGrammar.E.CallSquare;
import fearlessFullGrammar.E.DeclarationLiteral;
import fearlessFullGrammar.E.Implicit;
import fearlessFullGrammar.E.Literal;
import fearlessFullGrammar.E.Round;
import fearlessFullGrammar.E.StringInter;
import fearlessFullGrammar.E.TypedLiteral;
import fearlessFullGrammar.E.X;
import fearlessFullGrammar.EVisitor;
import fearlessFullGrammar.M;
import fearlessFullGrammar.Parameter;
import fearlessFullGrammar.Sig;
import fearlessFullGrammar.T.RCC;
import fearlessFullGrammar.XPat;

public class HasImplicitVisitor implements EVisitor<Boolean>{
  @Override public Boolean visitX(X n){ return false; }
  @Override public Boolean visitRound(Round r){ return r.e().accept(this); }
  @Override public Boolean visitImplicit(Implicit n){ return true; }
  @Override public Boolean visitTypedLiteral(TypedLiteral t){ return false; }
  @Override public Boolean visitDeclarationLiteral(DeclarationLiteral c){ return false; }
  @Override public Boolean visitLiteral(Literal c){ return false; }
  @Override public Boolean visitCall(Call c){
    return c.e().accept(this)
      || c.es().stream().anyMatch(e->e.accept(this));
  }
  @Override public Boolean visitStringInter(StringInter i){
    return i.e().map(e0->e0.accept(this)).orElse(false)
      || i.es().stream().anyMatch(e->e.accept(this));
  }
  @Override public CallSquare visitInnerCallSquare(CallSquare c){ return c; }
  @Override public RCC visitInnerRCC(RCC t){ return t; }
  @Override public XPat visitInnerXPat(XPat x){ return x; }
  @Override public M visitInnerM(M m){ return m; }
  @Override public Sig visitInnerSig(Sig s){ return s; }
  @Override public Parameter visitInnerParameter(Parameter p){ return p; }
  @Override public B visitInnerB(B b){ return b; }
  @Override public Literal visitInnerLiteral(Literal l){ return l; }
  @Override public Declaration visitInnerDeclaration(Declaration d){ return d; }
}
