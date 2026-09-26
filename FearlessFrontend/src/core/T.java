package core;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;

import metaParser.Span;
import utils.Join;

public sealed interface T{
  TSpan span();
  record X(String name, TSpan span) implements T{
    public X{ assert validate(name,"generic type name", _XId); }
    public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements T{
    public RCX{ assert nonNull(rc,x); }
    public String toString(){ return rc.name()+" "+x.name; }
    public TSpan span(){ return x.span();}
    public Optional<RC> explicitRC(){ return Optional.of(rc); }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{ assert nonNull(x); }
    public String toString(){ return "read/imm "+x.name; }
    public TSpan span(){ return x.span();}
  }
  record C(TName name, List<T> ts) implements KindingTarget{
    public C{
      assert unmodifiable(ts,"T.C.args");
      assert eq(ts.size(), name.arity(),"Type arity");
    }
    public String toString(){
      return name.s()+Join.of(ts,"[",",","]","");
    }
    public C withTs(List<T> ts){ return new C(name,ts); }
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
    public String toString(){ return rc.toStrSpace() + c; }
    public RCC withTs(List<T> ts){ return new RCC(rc,c.withTs(ts),span); }
    public RCC withRC(RC rc){ return new RCC(rc,c,span); }
    public Optional<RC> explicitRC(){ return Optional.of(rc); }
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
  default Optional<RC> explicitRC(){ return Optional.empty(); }
  default boolean explicitH(){ return explicitRC().stream().anyMatch(rc->rc == RC.readH || rc == RC.mutH); }
}