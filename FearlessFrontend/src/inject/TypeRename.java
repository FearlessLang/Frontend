package inject;

import java.util.List;
import java.util.Optional;

import core.RC;
import core.T;
import core.TName;
import core.TSpan;
import utils.Pos;
import inference.IT;

public class TypeRename{
  public static T of(T t, List<String> xs, List<T> ts){
    assert xs.size() == ts.size();
    if (xs.isEmpty()){ return t; }
    return switch (t){
      case T.X x -> getOrSame(x,x.name(),xs,ts);
      case T.RCX(RC rc, var x) -> of(x,xs,ts).withRC(rc);
      case T.RCC rcc -> rcc.withTs(ofT(rcc.c().ts(),xs,ts));
      case T.ReadImmX(var x) -> of(x,xs,ts).readImm();
    };
  }
  //TODO: much code could be made faster if instead of xs+ts being list, they were Function<Integer,XX>..
  //no, we need get, size and indexof. But, what about a single data structure that pairs them somehow?
  public static List<T> ofT(List<T> tsi ,List<String> xs, List<T> ts){
    if (xs.isEmpty()){ return tsi; }
    return tsi.stream().map(ti->of(ti,xs,ts)).toList();
  }
  public static IT of(IT t, List<String> xs, List<IT> ts){
    assert xs.size() == ts.size();
    if (xs.isEmpty()){ return t; }
    return switch (t){
      case IT.X x -> getOrSame(x,x.name(),xs,ts);
      case IT.RCX(RC rc, var x) -> of(x,xs,ts).withRC(rc);
      case IT.RCC rcc -> rcc.withTs(ofIT(rcc.c().ts(),xs,ts));
      case IT.ReadImmX(var x) -> of(x,xs,ts).readImm();
      case IT.U u -> u;
      case IT.Err e -> e;
    };
  }
  public static List<IT> ofIT(List<IT> tsi ,List<String> xs, List<IT> ts){
    if (xs.isEmpty()){ return tsi; }
    return tsi.stream().map(ti->of(ti,xs,ts)).toList(); }
  public static List<IT.C> ofITC(List<IT.C> csi, List<String> xs, List<IT> ts){
    if (xs.isEmpty()){ return csi; }
    return csi.stream().map(c->of(c,xs,ts)).toList();
  }
  public static IT.C of(IT.C c, List<String> xs, List<IT> ts){
    if (xs.isEmpty()){ return c; }
    return new IT.C(c.name(), ofIT(c.ts(),xs,ts));
  }
  public static List<Optional<IT>> ofITOpt(List<IT> tsi ,List<String> xs, List<IT> ts){ return tsi.stream().map(ti->Optional.of(of(ti,xs,ts))).toList(); }
  public static List<Optional<IT>> ofOptITOpt(List<Optional<IT>> tsi ,List<String> xs, List<IT> ts){ return tsi.stream().map(ti->Optional.of(of(ti.get(),xs,ts))).toList(); }
  public static <A> A getOrSame(A x, String name, List<String> xs, List<A> ts){
    var i= xs.indexOf(name); 
    return i == -1 ? x : ts.get(i);
  }
  public static List<IT.C> tcToITC(List<T.C> cs){ return cs.stream().map(TypeRename::tcToITC).toList(); }
  public static List<IT> tToIT(List<T> cs){ return cs.stream().map(TypeRename::tToIT).toList(); }
  public static List<T> itToT(List<IT> cs){ return cs.stream().map(TypeRename::itToT).toList(); }
  public static List<T> itOptToT(List<Optional<IT>> ts){ return ts.stream().map(ti->itToT(ti)).toList(); }
  public static T itToT(Optional<IT> t){ return t.map(ti->itToT(ti)).orElse(inferUnknown); }
  public static T.C itcToTC(IT.C c){ return new T.C(c.name(),c.ts().stream().map(ti->itToT(ti)).toList()); }
  public static List<T.C> itcToTC(List<IT.C> cs){
    return cs.stream().map(TypeRename::itcToTC).toList();  
  }
  public static IT.C tcToITC(T.C c){
    return new IT.C(c.name(),c.ts().stream().map(ti->tToIT(ti)).toList());
  }
  public static IT tToIT(T t){return switch (t){
    case T.X(var name,var span) -> new IT.X(name,span);
    case T.ReadImmX(var x) -> new IT.ReadImmX(new IT.X(x.name(),x.span()));
    case T.RCX(var rc,var x) -> new IT.RCX(rc,new IT.X(x.name(),x.span()));
    case T.RCC(var rc, var c,var span) -> new IT.RCC(rc,tcToITC(c),span);
  };}
  public static T itToT(IT t){return switch (t){
    case IT.X(var name, var span) -> new T.X(name,span);
    case IT.ReadImmX(var x) -> new T.ReadImmX(new T.X(x.name(),x.span()));
    case IT.RCX(var rc,var x) -> new T.RCX(rc,new T.X(x.name(),x.span()));
    case IT.RCC(var rc, var c, var span) -> new T.RCC(rc,itcToTC(c),span);
    case IT.U _ ->inferUnknown;
     //throw Bug.of();// bug is good for testing, it will be replaced with this later: inferUnknown;
    case IT.Err(var cfs,_)  ->
    //throw Bug.of();//
    inferErr(cfs.stream().map(TypeRename::itToT).limit(4).toList());
  };}
  public static final T.RCC inferErr(List<T> conflicts){
    return new T.RCC(RC.imm,new T.C(new TName("base.InferErr", conflicts.size(), Pos.unknown), conflicts),TSpan.fromPos(Pos.unknown,1));
  }
  public static final T.RCC inferUnknown= new T.RCC(RC.imm,new T.C(new TName("base.InferUnknown", 0, Pos.unknown), List.of()),TSpan.fromPos(Pos.unknown,1));
}