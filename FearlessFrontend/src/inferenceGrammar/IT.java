package inferenceGrammar;

import static fearlessParser.TokenKind._XId;
import static fearlessParser.TokenKind.validate;
import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;
import java.util.stream.Collectors;

import fearlessFullGrammar.TName;
import fearlessParser.RC;

public sealed interface IT {
  default boolean isTV(){ return true; }
  record X(String name) implements IT{
    public X{ assert validate(name,"generic type name", _XId); }
    public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements IT{
    public RCX{assert nonNull(rc,x);}
    public String toString(){ return rc.name()+" "+x.name; }
  }
  record ReadImmX(X x) implements IT{
    public ReadImmX{assert nonNull(x);}
    public String toString(){ return "read/imm "+x.name; }
  }
  record C(TName name, List<IT> ts){
    public C{
      assert unmodifiable(ts,"T.C.args");
      assert eq(ts.size(), name.arity(),"Type arity");
    }
    public String toString(){ return name.s()+"["+ts.stream().map(Object::toString).collect(Collectors.joining(","))+"]"; }
  }
  record RCC(RC rc, C c) implements IT{
    public RCC{ nonNull(rc,c); }
    public String toString(){ return rc.name()+" "+c; }
    public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); }
  }
  enum U implements IT{ Instance; 
    public String toString(){ return "?";}
    public boolean isTV(){ return false; }
  }
}