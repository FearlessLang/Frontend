package inference;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;

import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import fearlessParser.RC;
import utils.Bug;
import utils.Join;

public sealed interface IT {
  default boolean isTV(){ return true; }
  TSpan span();
  record X(String name, TSpan span) implements IT{
    public X{ assert validate(name,"generic type name", _XId); }
    public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements IT{
    public RCX{assert nonNull(rc,x);}
    public String toString(){ return rc.name()+" "+x.name; }
    public TSpan span(){ return x.span();}
  }
  record ReadImmX(X x) implements IT{
    public ReadImmX{assert nonNull(x);}
    public String toString(){ return "read/imm "+x.name; }
    public TSpan span(){ return x.span();}
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
  record RCC(RC rc, C c, TSpan span) implements IT{
    public RCC{ nonNull(rc,c); }
    public String toString(){ return rc.toStrSpace()+c; }
    public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); }
    public RCC withTs(List<IT> ts){
      if (ts == c.ts()){ return this; }
      return new RCC(rc,new C(c.name(),ts),span);
    }
    public RCC withRCTs(RC rc,List<IT> ts){
      if (rc == this.rc && ts == c.ts()){ return this; }
      return new RCC(rc,new C(c.name(),ts),span);
    }
  }
  enum U implements IT{ Instance; 
    public String toString(){ return "?";}
    public boolean isTV(){ return false; }
    public TSpan span(){throw Bug.unreachable(); }
  }
  enum Err implements IT{ Instance; 
    public String toString(){ return "Err";}
    public TSpan span(){throw Bug.unreachable(); }
  }
  default IT withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(var _, var c, var span) -> new RCC(rc, c, span);
    case RCX(var _, var x) -> new RCX(rc, x);
    case X x -> new RCX(rc, x);
    case ReadImmX(var x) -> new RCX(rc, x);
    case IT.U _   -> throw Bug.unreachable();
    case IT.Err _ -> throw Bug.unreachable();
  };}
  default IT readImm(){ return switch (this){ // T[read/imm]
    case X x -> new ReadImmX(x);
    case ReadImmX _ -> this;
    case RCC(var rc, var c, var span) -> new RCC(rc.readImm(), c, span);
    case RCX(var rc, var x) -> new RCX(rc.readImm(), x);
    case U _   -> this;
    case Err _ -> this;
  };}
}