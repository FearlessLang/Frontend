package typeSystem;

import java.util.List;
import java.util.Objects;
import java.util.function.Function;

import core.*;
import core.E.*;
import utils.Streams;
import typeSystem.Change.*;

public record Gamma(Gamma tail, String name, T t, Change current){
  private static final Gamma _empty= new Gamma(null,null,null,null);
  public static Gamma empty(){ return _empty; }
  public Gamma add(String name, T t){ return new Gamma(this, name, t,new Same(t)); }
  public Gamma map(Function<Change,Change> f){
    if (this == _empty){ return this; }
    return new Gamma(tail.map(f), name, t, f.apply(current));
  }
  public Gamma addAll(List<T> ts, List<String> xs){ return Streams.zip(xs, ts).fold(Gamma::add, this); }
  public record Binding(T declared, Change current){}
  public Binding bind(String x){ return Objects.requireNonNull(_bindOrNull(x)); }
  public Binding _bindOrNull(String x){
    if (this == _empty){ return null; }
    if (name.equals(x)){ return new Binding(t, current); }
    return tail._bindOrNull(x);
  }
  public Gamma filterFTV(Literal l){
    return filterFTV(l,LiteralDeclarations.has(l.cs(),LiteralDeclarations.captureFree));
  }
  private Gamma filterFTV(Literal l,boolean captureFree){//we only care about dom(bs)
    //\u0393|Xs= {x : T | x : T \u2208 \u0393 \u2227 FTV(T) \u2286 Xs}
    if (this == _empty){ return this; }
    var rest= tail.filterFTV(l,captureFree);
    if (captureFree){ return new Gamma(rest, name, t, new Change.CapFree(l,t)); }
    if (current instanceof Change.WithT w && !hasOnlyFTV(w.currentT(),l.bs())){ return new Gamma(rest, name, t, new Change.DropFTV(l, w.currentT())); }
    return new Gamma(rest, name, t, current);//core.E.Literal l, core.M m, T atDrop
  }
  //Above can not reuse FreeXs since FreeXs works on IT
  boolean hasOnlyFTV(T t, List<B> bs){ return switch (t){
    case T.X x -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.RCX(_, var x) -> hasOnlyFTV(x,bs);
    case T.ReadImmX(var x) -> hasOnlyFTV(x,bs);
    case T.RCC(_, var c,_) -> c.ts().stream().allMatch(ti->hasOnlyFTV(ti,bs));
  };}
}
//Deliberately simple: \u0393 never gets deeper than 18 (2.33 on average), and all of its
//map/filterFTV/bind work is ~2.4ms of a ~500ms compile of base. A flat or lazy \u0393 wins <1%.