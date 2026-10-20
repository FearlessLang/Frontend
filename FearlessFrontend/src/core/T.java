package core;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;

import message.WellFormednessErrors;
import metaParser.Span;
import utils.Join;

public sealed interface T{
  TSpan span();
  default int depth(){ return 1; }
  record X(String name, TSpan span) implements T{
    public X{ assert validate(name, "generic type name", _XId); }
    @Override public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements T{
    public RCX{ assert nonNull(rc, x); }
    @Override public String toString(){ return rc.name()+" "+x.name; }
    @Override public TSpan span(){ return x.span();}
    @Override public Optional<RC> explicitRC(){ return Optional.of(rc); }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{ assert nonNull(x); }
    @Override public String toString(){ return "read/imm "+x.name; }
    @Override public TSpan span(){ return x.span();}
  }
  record C(TName name, List<T> ts, int depth) implements KindingTarget{
    public static final int maxDepth= 100;
    public C{
      assert unmodifiable(ts, "T.C.ts");
      assert eq(ts.size(), name.arity(), "Type arity");
      if (depth > maxDepth){ throw WellFormednessErrors.instantiatedTooDeep(name); }
    }
    public C(TName name, List<T> ts){ this(name, ts, 1+ts.stream().mapToInt(T::depth).max().orElse(1)); }
    @Override public String toString(){
      return name.s()+Join.of(ts, "[", ",", "]", "");
    }
    public C withTs(List<T> ts){ return new C(name, ts); }
    @Override public TSpan span(){
      var start= name.pos();
      if (ts.isEmpty()){ return TSpan.fromPos(start, name.s().length()); }
      var end= ts.getLast().span().inner;
      var len= end.endCol() - start.column();
      var bad= len <= 0 || end.endLine() < start.line();
      if (bad){ return TSpan.fromPos(start, name.s().length()); }
      return new TSpan(new Span(start.fileName(),
        start.line(), start.column(),
        end.endLine(), end.endCol()+1));//the closing "]"
    }
  }
  record RCC(RC rc, C c, TSpan span) implements T{
    public RCC{ assert nonNull(rc, c); }
    @Override public String toString(){ return rc.toStrSpace() + c; }
    public RCC withTs(List<T> ts){ return new RCC(rc, c.withTs(ts), span); }
    @Override public int depth(){ return c.depth(); }
    @Override public RCC withRC(RC rc){ return new RCC(rc, c, span); }
    @Override public Optional<RC> explicitRC(){ return Optional.of(rc); }
  }
  default T withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(_, var c, var span) -> new RCC(rc, c, span);
    case RCX(_, var x) -> new RCX(rc, x);
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
  default boolean explicitH(){ return explicitRC().stream().anyMatch(RC::isH); }
}