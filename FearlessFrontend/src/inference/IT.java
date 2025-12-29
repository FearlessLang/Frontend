package inference;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.stream.Stream;

import core.RC;
import core.TName;
import core.TSpan;
import message.WellFormednessErrors;
import utils.Bug;
import utils.Join;

public sealed interface IT {
  default boolean isTV(){ return true; }
  default long badness(){ return 0; }
  TSpan span();
  default int depth(){ return 1; }
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
  record C(TName name, List<IT> ts, int depth){
    public C{
      assert unmodifiable(ts,"T.C.args");
      assert eq(ts.size(), name.arity(),"Type arity");
    }
    public C(TName name, List<IT> ts){ this(name,ts,RCC.depthFromTs(ts)); }
    public String toString(){
      if (ts.isEmpty()){ return name.s(); } 
      return name.s()+Join.of(ts,"[",",","]",""); 
    }
  }
  record RCC(RC rc, C c, TSpan span) implements IT{
    static final int maxDepth=100;
    public RCC(RC rc, C c, TSpan span){
      nonNull(rc,c);
      this.rc=rc; this.c=c; this.span= span;
      if (c.depth() > maxDepth){ throw new WellFormednessErrors.ErrToFetchContext(this); }
    }
    static int depthFromTs(List<IT> ts){ return 1+ts.stream().mapToInt(IT::depth).max().orElse(1); }
    static RCC ofOr(RCC fallback, RC rc, TName name, List<IT> ts, TSpan span){
      int depth= depthFromTs(ts);
      if (depth > maxDepth){ return fallback; }
      return new RCC(rc, new C(name, ts, depth), span);
    }
    public RCC withTs(List<IT> ts){
      if (ts == c.ts()){ return this; }
      return ofOr(this, rc, c.name(), ts, span);
    }
    public RCC withRCTs(RC rc, List<IT> ts){
      if (rc == this.rc && ts == c.ts()){ return this; }
      if (ts == c.ts()){ return new RCC(rc, c, span); }
      return ofOr(this, rc, c.name(), ts, span);
    }
    public long badness(){ return c.ts.stream().mapToLong(IT::badness).sum(); }
    public String toString(){ return rc.toStrSpace()+c; }
    public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); }
    public int depth(){ return c.depth(); }
  }
  enum U implements IT{ Instance; 
    public String toString(){ return "?";}
    public boolean isTV(){ return false; }
    public TSpan span(){throw Bug.unreachable(); }
    public long badness(){ return 1; }
  }
  record Err(List<IT> conflicts, int depth) implements IT{
    public Err{ assert depth < 10; }
    public Err(List<IT> conflicts){ this(conflicts,conflicts.stream().mapToInt(IT::depth).max().getAsInt()); }
    public String toString(){ return "Err";}
    public TSpan span(){throw Bug.unreachable(); }
    public long badness(){ return 1_000_000; }
    public static Err merge(IT t1, IT t2){ return switch (t1){
      case Err(var cs1,_) -> switch (t2){
        case Err(var cs2,_) -> new Err(Stream.concat(cs1.stream(),cs2.stream()).distinct().toList());
        default -> new Err(Stream.concat(cs1.stream(),Stream.of(t2)).distinct().toList());
      };
      default -> switch (t2){
        case Err(var cs2,_) -> new Err(Stream.concat(Stream.of(t1),cs2.stream()).distinct().toList());
        default -> new Err(List.of(t1,t2));
      };
    };}
  }
  default IT withRC(RC rc){ return switch (this){ // T[RC]
    case RCC(var _, var c, var span) -> new RCC(rc, c, span);
    case RCX(var _, var x) -> new RCX(rc, x);
    case X x -> new RCX(rc, x);
    case ReadImmX(var x) -> new RCX(rc, x);
    case IT.U _   -> this;
    case IT.Err _ -> this;
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