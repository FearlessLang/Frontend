package fearlessFullGrammar;

public interface TVisitor<R>{
  R visitTX(T.X x);
  R visitRCX(T.RCX x);
  R visitReadImmX(T.ReadImmX x);
  R visitRCC(T.RCC c);
}