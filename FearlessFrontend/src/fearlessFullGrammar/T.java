package fearlessFullGrammar;

import static fearlessParser.TokenKind._XId;
import static fearlessParser.TokenKind.validate;
import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;
import static offensiveUtils.Require.validOpt;

import java.util.List;
import java.util.Optional;

import fearlessParser.RC;

public sealed interface T {
  <R> R accept(TVisitor<R> v);
  record X(String name) implements T{
    public X{assert validate(name,"generic type name", _XId);}
    public <R> R accept(TVisitor<R> v){ return v.visitX(this); }
  }
  record RCX(RC rc, X x) implements T{
    public RCX{assert nonNull(rc,x);}
    public <R> R accept(TVisitor<R> v){ return v.visitRCX(this); }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{assert nonNull(x);}
    public <R> R accept(TVisitor<R> v){ return v.visitReadImmX(this); }
  }
  record C(TName name, Optional<List<T>> ts){
    public C{
      assert validOpt(ts,_ts->{
        unmodifiable(_ts,"T.C.args");
        eq(_ts.size(), name.arity(),"Type arity");
      });
    }
  }
  record RCC(Optional<RC> rc, C c) implements T{
    public RCC{ nonNull(rc,c); }
    public <R> R accept(TVisitor<R> v){ return v.visitRCC(this); }
  }
}