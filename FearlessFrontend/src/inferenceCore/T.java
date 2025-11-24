package inferenceCore;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;
import java.util.stream.Collectors;

import fearlessFullGrammar.TName;
import fearlessParser.RC;

public sealed interface T {
  record X(String name) implements T{
    public X{ assert validate(name,"generic type name", _XId); }
    public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements T{
    public RCX{assert nonNull(rc,x);}
    public String toString(){ return rc.name()+" "+x.name; }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{assert nonNull(x);}
    public String toString(){ return "read/imm "+x.name; }
  }
  record C(TName name, List<T> ts){
    public C{
      assert unmodifiable(ts,"T.C.args");
      assert eq(ts.size(), name.arity(),"Type arity");
    }
    public String toString(){
      if (ts.isEmpty()){ return name.s(); }
      return name.s()+"["+ts.stream().map(Object::toString).collect(Collectors.joining(","))+"]";
    }
  }
  record RCC(RC rc, C c) implements T{
    public RCC{ nonNull(rc,c); }
    public String toString(){
      if (rc == RC.imm){ return c.toString(); }
      return rc.name()+" "+c;
    }
  }
}