package fearlessFullGrammar;

public interface EVisitor<R>{
  R visitX(E.X n);
  R visitRound(E.Round r);
  R visitImplicit(E.Implicit n);
  R visitTypedLiteral(E.TypedLiteral t);
  R visitDeclarationLiteral(E.DeclarationLiteral c);
  R visitLiteral(E.Literal c);
  R visitCall(E.Call c);
  R visitStringInter(E.StringInter i);
}