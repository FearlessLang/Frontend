package fearlessFullGrammar;

import java.util.List;
import java.util.function.Function;

import fearlessParser.RC;

public interface TVisitor<R>{
  R visitTX(T.X x);
  R visitRCX(T.RCX x);
  R visitReadImmX(T.ReadImmX x);
  R visitRCC(T.RCC c);
  default TName visitInnerTName(TName n){ return n; }
  default T.X   visitInnerX(T.X x){ return x; }
  default T.C   visitInnerC(T.C c){ return c; }
  default RC    visitInnerRC(RC rc){ return rc; }
  default <RR> List<RR> mapTs(List<T> ts, Function<T,RR> f){ return ts.stream().map(f).toList(); }
}