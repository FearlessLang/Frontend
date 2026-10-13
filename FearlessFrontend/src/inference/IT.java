package inference;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import core.RC;
import core.TName;
import core.TSpan;
import message.WellFormednessErrors;
import utils.Join;

public sealed interface IT{
  default boolean isTV(){ return true; }
  default long badness(){ return 0; }
  default Optional<RC> explicitRC(){ return Optional.empty(); }
  default int depth(){ return 1; }
  record X(String name, TSpan span) implements IT{
    public X{ assert validate(name, "generic type name", _XId); }
    @Override public String toString(){ return name; }
  }
  record RCX(RC rc, X x) implements IT{
    public RCX{ assert nonNull(rc, x); }
    @Override public String toString(){ return rc.name()+" "+x.name; }
    @Override public Optional<RC> explicitRC(){ return Optional.of(rc); }
  }
  record ReadImmX(X x) implements IT{
    public ReadImmX{ assert nonNull(x); }
    @Override public String toString(){ return "read/imm "+x.name; }
  }
  record C(TName name, List<IT> ts, int depth){
    public C{
      assert unmodifiable(ts, "IT.C.ts");
      assert eq(ts.size(), name.arity(), "Type arity");
    }
    public C(TName name, List<IT> ts){ this(name, ts, RCC.depthFromTs(ts)); }
    @Override public String toString(){
      return name.s()+Join.of(ts, "[", ",", "]", "");
    }
  }
  record RCC(Optional<RC> rc, C c, TSpan span) implements IT{
    static final int maxDepth= 100;
    public RCC(Optional<RC> rc, C c, TSpan span){
      assert nonNull(rc, c);
      this.rc= rc; this.c= c; this.span= span;
      if (c.depth() > maxDepth){ throw new WellFormednessErrors.ErrToFetchContext(this); }
    }
    static int depthFromTs(List<IT> ts){ return 1+ts.stream().mapToInt(IT::depth).max().orElse(1); }
    public RCC withTs(List<IT> ts){ return withRCTs(rc, ts); }
    public RCC withRCTs(Optional<RC> rc, List<IT> ts){
      var depth= depthFromTs(ts);
      if (depth > maxDepth){ return this; }
      return new RCC(rc, new C(c.name(), ts, depth), span);
    }
    @Override public long badness(){ return c.ts.stream().mapToLong(IT::badness).sum(); }
    @Override public String toString(){ return rc.map(RC::toStrSpace).orElse("AnyRC ")+c; }
    @Override public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); }
    @Override public int depth(){ return c.depth(); }
    @Override public Optional<RC> explicitRC(){ return rc; }
  }
  enum U implements IT{ Instance;
    @Override public String toString(){ return "?";}
    @Override public boolean isTV(){ return false; }
    @Override public long badness(){ return 1; }
  }
  default IT withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(_, var c, var span) -> new RCC(Optional.of(rc), c, span);
    case RCX(_, var x) -> new RCX(rc, x);
    case X x -> new RCX(rc, x);
    case ReadImmX(var x) -> new RCX(rc, x);
    case U _   -> this;
  };}
  default Stream<String> ftv(){ return switch (this){
    case X(var name, _) -> Stream.of(name);
    case RCX(_, var x) -> x.ftv();
    case ReadImmX(var x) -> x.ftv();
    case RCC(_, var c, _) -> c.ts().stream().flatMap(IT::ftv);
    case U _ -> Stream.of();
  };}
  default IT readImm(){ return switch (this){ // T[read/imm]
    case X x -> new ReadImmX(x);
    case ReadImmX _ -> this;
    case RCC(var rc, var c, var span) -> new RCC(rc.map(RC::readImm), c, span);
    case RCX(var rc, var x) -> new RCX(rc.readImm(), x);
    case U _   -> this;
  };}
}