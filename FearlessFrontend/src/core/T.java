package core;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;

import fearlessFullGrammar.TName;
import fearlessParser.RC;
import message.Join;

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
      return name.s()+Join.of(ts,"[",",","]","");
    }
  }
  record RCC(RC rc, C c) implements T{
    public RCC{ assert nonNull(rc,c); }
    public String toString(){
      if (rc == RC.imm){ return c.toString(); }
      return rc.name()+" "+c;
    }
    public RCC withTs(List<T> ts){
      if (ts == c.ts()){ return this; }
      return new RCC(rc,new C(c.name(),ts));
    }

  }
  default T withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(var _, var c) -> new RCC(rc, c);
    case RCX(var _, var x) -> new RCX(rc, x);
    case X x -> new RCX(rc, x);
    case ReadImmX(var x) -> new RCX(rc, x);
  };}
  default T readImm(){ return switch (this){ // T[read/imm]
    case X x -> new ReadImmX(x);
    case ReadImmX _ -> this;
    case RCC(var rc, var c) -> new RCC(rc.readImm(), c);
    case RCX(var rc, var x) -> new RCX(rc.readImm(), x);
  };}
}