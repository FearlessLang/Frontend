package core;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;

import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import fearlessParser.RC;
import message.Join;
import metaParser.Span;

public sealed interface T {
  TSpan span();
  record X(String name, TSpan span) implements T{
    public X{ assert validate(name,"generic type name", _XId); }
    public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements T{
    public RCX{assert nonNull(rc,x);}
    public String toString(){ return rc.name()+" "+x.name; }
    public RCX withRC(RC rc){
      if (rc == this.rc){ return this; }
      return new RCX(rc,x);
    }
    public TSpan span(){ return x.span();}
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{assert nonNull(x);}
    public String toString(){ return "read/imm "+x.name; }
    public TSpan span(){ return x.span();}
  }
  record C(TName name, List<T> ts) implements KindingTarget{
    public C{
      assert unmodifiable(ts,"T.C.args");
      assert eq(ts.size(), name.arity(),"Type arity");
    }
    public String toString(){
      if (ts.isEmpty()){ return name.s(); }
      return name.s()+Join.of(ts,"[",",","]","");
    }
    public TSpan span(){    
      var start= name.pos();
      if (ts.isEmpty()){ return TSpan.fromPos(start,name.s().length()); }
      var end= ts.getLast().span().inner;
      int len= end.endCol() - start.column();
      var bad= len <= 0 || end.endLine() < start.line();
      if (bad){ return TSpan.fromPos(start,name.s().length()); }
      return new TSpan(new Span(start.fileName(),
        start.line(),start.column(),
        end.endLine(),end.endCol()+1));//the closing "]"
    }
  }
  record RCC(RC rc, C c, TSpan span) implements T, KindingTarget{
    public RCC{ assert nonNull(rc,c); }
    public String toString(){
      if (rc == RC.imm){ return c.toString(); }
      return rc.name()+" "+c;
    }
    public RCC withTs(List<T> ts){
      if (ts == c.ts()){ return this; }
      return new RCC(rc,new C(c.name(),ts),span);
    }
    public RCC withRC(RC rc){
      if (rc == this.rc){ return this; }
      return new RCC(rc,c,span);
    }
  }
  default T withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(var _, var c,var span) -> new RCC(rc, c, span);
    case RCX(var _, var x) -> new RCX(rc, x);
    case X x -> new RCX(rc, x);
    case ReadImmX(var x) -> new RCX(rc, x);
  };}
  default T readImm(){ return switch (this){ // T[read/imm]
    case X x -> new ReadImmX(x);
    case ReadImmX _ -> this;
    case RCC(var rc, var c, var span) -> new RCC(rc.readImm(), c, span);
    case RCX(var rc, var x) -> new RCX(rc.readImm(), x);
  };}
}