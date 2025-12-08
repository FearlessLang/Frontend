package typeSystem;

import static offensiveUtils.Require.eq;

import java.util.List;
import java.util.function.Function;

import core.*;
import core.E.*;
import message.TypeSystemErrors;
import utils.Bug;
import typeSystem.Change.*;

public record Gamma(Gamma tail, String name, T t, Change current){
  private static final Gamma _empty= new Gamma(null,null,null,null);
  public static Gamma empty(){ return _empty; }
  public Gamma add(String name, T t){ return new Gamma(this, name, t,new Same(t)); }
  public Gamma mapFilter(Function<T,Change> f){
    if (this == _empty){ return this; }
    var rest= tail.mapFilter(f);
    return new Gamma(rest, name, t, current.map(f));
  }
  public Gamma addAll(List<T> ts, List<String> xs){
    var res= this;
    assert eq(xs.size(),ts.size(),"Arity mismatch in bodyOk");
    for(int i= 0; i < xs.size(); i++){ res = res.add(xs.get(i),ts.get(i)); }
    return res;
  }
  public record Binding(T declared, Change current){}
  public Binding bind(String x){
    if (this == _empty){ throw Bug.of(); }
    if (name.equals(x)){ return new Binding(t, current); }
    return tail.bind(x);
  }
  public T get(String x){
    if (this == _empty){ throw Bug.of(); }
    if (name.equals(x)){ return current.view().get(); }
    return tail.get(x);
  }
  public Gamma filterFTV(Literal l){//we only care about dom(bs)
    //Γ|Xs= {x : T | x : T ∈ Γ ∧ FTV(T) ⊆ Xs}
    if (this == _empty){ return this; }
    var rest= tail.filterFTV(l);
    var v= current.view();
    if (v.isEmpty()){ return new Gamma(rest, name, t, current); }//core.E.Literal l, core.M m, T atDrop
    if (!hasOnlyFTV(v.get(),l.bs())){ return new Gamma(rest, name, t, new Drop(TypeSystemErrors.filterFTVWhy(l,v.get()))); }
    return new Gamma(rest, name, t, current);
  }
  //Above can not reuse FreeXs since FreeXs works on IT
  boolean hasOnlyFTV(T t, List<B> bs){ return switch (t){
    case T.X x -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.RCX(_, var x) -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.ReadImmX(var x) -> bs.stream().anyMatch(b->b.x().equals(x.name()));
    case T.RCC(_, var c) -> c.ts().stream().allMatch(ti->hasOnlyFTV(ti,bs));
  };}
}
//TODO: bad toy impl!