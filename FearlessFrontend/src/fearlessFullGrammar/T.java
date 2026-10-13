package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;

import core.RC;
import core.TName;
import core.TSpan;

public sealed interface T{
  record X(String name, TSpan span) implements T{
    public X{ assert validate(name,"generic type name", _XId); }
    public String toString(){ return "X[name="+name+"]";}
  }
  record RCX(RC rc, X x) implements T{
    public RCX{ assert nonNull(rc,x); }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{ assert nonNull(x); }
  }
  record C(TName name, Optional<List<T>> ts){
    public C{
      assert validOpt(ts,_ts->{
        unmodifiable(_ts,"T.C.ts");
        eq(_ts.size(), name.arity(),"Type arity");
      });
    }
  }
  record RCC(Optional<RC> rc, C c,TSpan span) implements T{
    public RCC{ assert nonNull(rc,c); }
    public String toString(){ return "RCC[rc="+rc+",c="+c+"]"; }
  }
}