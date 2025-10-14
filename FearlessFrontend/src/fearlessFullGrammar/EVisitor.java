package fearlessFullGrammar;

public interface EVisitor<R>{
  R visitX(E.X n);
  R visitRound(E.Round r);
  R visitImplicit(E.Implicit n);
  R visitTypedLiteral(E.TypedLiteral t);
  T.RCC visitInnerRCC(T.RCC t);
  R visitDeclarationLiteral(E.DeclarationLiteral c);
  R visitLiteral(E.Literal c);
  R visitCall(E.Call c);
  E.CallSquare visitInnerCallSquare(E.CallSquare c);
  R visitStringInter(E.StringInter i);
  XPat visitInnerXPat(XPat x);
  M visitInnerM(M m);
  Sig visitInnerSig(Sig s);
  Parameter visitInnerParameter(Parameter p);
  B visitInnerB(B b);
  E.Literal visitInnerLiteral(E.Literal l);
  Declaration visitInnerDeclaration(Declaration d);
  default MName visitInnerMName(MName n){ return n; }
  default E.X visitInnerX(E.X n){ return n; }
  //default <RR> List<RR> mapEs(List<E> es, Function<E,RR> f){ return es.stream().map(f).toList(); }
  //default <RR> List<RR> mapBs(List<B> bs, Function<B,RR> f){ return bs.stream().map(f).toList(); }
  //default <RR> List<RR> mapPs(List<Parameter> ps, Function<Parameter,RR> f){ return ps.stream().map(f).toList(); }
}