package inference;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;

import fearlessFullGrammar.TName;
import fearlessParser.RC;
import message.Join;
import utils.Bug;

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
    public String toString(){
      if (ts.isEmpty()){ return name.s(); } 
      return name.s()+Join.of(ts,"[",",","]",""); 
    }
  }
  record RCC(RC rc, C c) implements IT{
    public RCC{ nonNull(rc,c); }
    public String toString(){ return rc==RC.imm? ""+c : rc.name()+" "+c; }
    public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); }
    public RCC withTs(List<IT> ts){
      if (ts == c.ts()){ return this; }
      return new RCC(rc,new C(c.name(),ts));
    }
  }
  enum U implements IT{ Instance; 
    public String toString(){ return "?";}
    public boolean isTV(){ return false; }
  }
  enum Err implements IT{ Instance; 
    public String toString(){ return "Err";}
    //public boolean isTV(){ return true; }//the default: We do accept Err as a real type
  }
  default IT withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(var _, var c) -> new RCC(rc, c);
    case RCX(var _, var x) -> new RCX(rc, x);
    case X x -> new RCX(rc, x);
    case ReadImmX(var x) -> new RCX(rc, x);
    case IT.U _   -> throw Bug.unreachable();
    case IT.Err _ -> throw Bug.unreachable();
  };}
  default IT readImm(){ return switch (this){ // T[read/imm]
    case X x -> new ReadImmX(x);
    case ReadImmX _ -> this;
    case RCC(var rc, var c) -> new RCC(rc.readImm(), c);
    case RCX(var rc, var x) -> new RCX(rc.readImm(), x);
    case U _   -> this;
    case Err _ -> this;
  };}
}