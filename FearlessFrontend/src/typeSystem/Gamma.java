package typeSystem;

import static offensiveUtils.Require.eq;

import java.util.List;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.function.Function;

import core.B;
import core.T;
import utils.Bug;

public record Gamma(Gamma tail, String name, T t){
  private static final Gamma _empty= new Gamma(null,null,null);
  public static Gamma empty(){ return _empty; }
  public Gamma add(String name, T t){ return new Gamma(this, name, t); }
  public Gamma mapFilter(BiFunction<String,T,Optional<T>> f){
    if (this == _empty){ return this; }
    var rest= tail.mapFilter(f);
    var ot= f.apply(name, t);
    return ot.map(nt -> rest.add(name, nt)).orElse(rest);
  }
  public Gamma mapFilter(Function<T,Optional<T>> f){
    if (this == _empty){ return this; }
    var rest= tail.mapFilter(f);
    var ot= f.apply(t);
    return ot.map(nt -> rest.add(name, nt)).orElse(rest);
  }
  public Gamma addAll(List<T> ts, List<String> xs){
    var res= this;
    assert eq(xs.size(),ts.size(),"Arity mismatch in bodyOk");
    for(int i= 0; i < xs.size(); i++){ res = res.add(xs.get(i),ts.get(i)); }
    return res;
  }
  public T get(String x){
    if (this == _empty){ throw Bug.of(); }
    if (name.equals(x)){ return t; }
    return tail.get(x);
  }
  public Gamma filterFTV(List<B> bs){//we only care about dom(bs)
    //Γ|Xs= {x : T | x : T ∈ Γ ∧ FTV(T) ⊆ Xs}
    if (this == _empty){ return this; }
    if (!hasOnlyFTV(t,bs)){ return tail.filterFTV(bs); }
    return tail.filterFTV(bs).add(name, t);
  }
  //Above can not reuse FreeXs since FreeXs works on IT
  boolean hasOnlyFTV(T t, List<B> bs){ return switch (t){
    case T.X x -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.RCX(_, var x) -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.ReadImmX(var x) -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.RCC(_, var c) -> c.ts().stream().allMatch(ti->hasOnlyFTV(ti,bs));
  };}
}//TODO: bad toy impl