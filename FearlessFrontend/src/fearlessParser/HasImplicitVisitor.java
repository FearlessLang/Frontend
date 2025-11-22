package fearlessParser;

import fearlessFullGrammar.E.Call;
import fearlessFullGrammar.E.DeclarationLiteral;
import fearlessFullGrammar.E.Implicit;
import fearlessFullGrammar.E.Literal;
import fearlessFullGrammar.E.Round;
import fearlessFullGrammar.E.StringInter;
import fearlessFullGrammar.E.TypedLiteral;
import fearlessFullGrammar.E.X;
import fearlessFullGrammar.EVisitor;

public class HasImplicitVisitor implements EVisitor<Boolean>{
  @Override public Boolean visitX(X n){ return false; }
  @Override public Boolean visitRound(Round r){ return r.e().accept(this); }
  @Override public Boolean visitImplicit(Implicit n){ return true; }
  //correctly not entering in literals. The :: is literal scoped, so a :: in the literal would be in the inner scope
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
}
