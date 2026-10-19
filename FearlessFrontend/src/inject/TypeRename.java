package inject;

import java.util.List;
import java.util.Optional;

import core.LiteralDeclarations;
import core.RC;
import core.T;
import core.TSpan;
import core.B;
import typeSystem.Kinding;
import utils.Streams;
import utils.Bug;
import utils.Pos;
import inference.IT;

public final class TypeRename{
  public static T of(T t, List<String> xs, List<T> ts){
    assert xs.size() == ts.size();
    return switch (t){
      case T.X x -> getOrSame(x, x.name(), xs, ts);
      case T.RCX(var rc, var x) -> withRC(of(x, xs, ts), rc);
      case T.RCC rcc -> rcc.withTs(ofT(rcc.c().ts(), xs, ts));
      case T.ReadImmX(var x) -> readImm(of(x, xs, ts));
    };
  }
  //TODO: much code could be made faster if instead of xs+ts being list, they were Function<Integer,XX>..
  //no, we need get, size and indexof. But, what about a single data structure that pairs them somehow?
  public static List<T> ofT(List<T> tsi , List<String> xs, List<T> ts){ return tsi.stream().map(ti -> of(ti, xs, ts)).toList(); }
  public static IT of(IT t, List<String> xs, List<IT> ts){
    assert xs.size() == ts.size();
    return switch (t){
      case IT.X x -> getOrSame(x, x.name(), xs, ts);
      case IT.RCX(var rc, var x) -> of(x, xs, ts).withRC(rc);
      case IT.RCC rcc -> rcc.withTs(ofIT(rcc.c().ts(), xs, ts));
      case IT.ReadImmX(var x) -> of(x, xs, ts).readImm();
      case IT.U _, IT.Amb _ -> t;
    };
  }
  public static List<IT> ofIT(List<IT> tsi , List<String> xs, List<IT> ts){ return tsi.stream().map(ti -> of(ti, xs, ts)).toList(); }
  public static IT.C of(IT.C c, List<String> xs, List<IT> ts){ return new IT.C(c.name(), ofIT(c.ts(), xs, ts)); }
  public static <A> A getOrSame(A x, String name, List<String> xs, List<A> ts){
    var i= xs.indexOf(name);
    return i == -1 ? x : ts.get(i);
  }
  public static List<IT> tToIT(List<T> cs){ return cs.stream().map(TypeRename::tToIT).toList(); }
  public static List<T> itToT(List<IT> cs){ return cs.stream().map(TypeRename::itToT).toList(); }
  public static T itToT(Optional<IT> t){ return itToT(t.orElseThrow(Bug::unreachable)); }
  public static T.C itcToTC(IT.C c){ return new T.C(c.name(), itToT(c.ts())); }
  public static List<T.C> itcToTC(List<IT.C> cs){ return cs.stream().map(TypeRename::itcToTC).toList(); }
  public static IT.C tcToITC(T.C c){ return new IT.C(c.name(), tToIT(c.ts())); }
  public static IT tToIT(T t){ return switch (t){
    case T.X(var name, var span) -> new IT.X(name, span);
    case T.ReadImmX(var x) -> new IT.ReadImmX(new IT.X(x.name(), x.span()));
    case T.RCX(var rc, var x) -> new IT.RCX(rc, new IT.X(x.name(), x.span()));
    case T.RCC(var rc, var c, var span) -> new IT.RCC(Optional.of(rc), tcToITC(c), span);
  };}
  public static T itToT(IT t){ return switch (t){
    case IT.X(var name, var span) -> new T.X(name, span);
    case IT.ReadImmX(var x) -> new T.ReadImmX(new T.X(x.name(), x.span()));
    case IT.RCX(var rc, var x) -> new T.RCX(rc, new T.X(x.name(), x.span()));
    case IT.RCC(var rc, var c, var span) -> new T.RCC(rc.orElse(RC.imm), itcToTC(c), span);
    case IT.U _, IT.Amb _ -> throw Bug.unreachable();
  };}
  public static boolean eqModXRC(List<B> bs, IT a, IT b){
    if (a.equals(b)){ return true; }
    if (!(a instanceof IT.RCC(var aRc, var aC, _) && b instanceof IT.RCC(var bRc, var bC, _))){
      if (!(a.withRC(RC.imm) instanceof IT.RCX(_, var x)) || !a.withRC(RC.imm).equals(b.withRC(RC.imm))){ return false; }
      return B.get(bs, x.name()).rcs().size() == 1 && Kinding.intrinsicRCs(bs, itToT(a)).equals(Kinding.intrinsicRCs(bs, itToT(b)));
    }
    var sameHead= aRc.orElse(RC.imm) == bRc.orElse(RC.imm) && aC.name().equals(bC.name());
    if (!sameHead){ return false; }
    return Streams.zip(aC.ts(), bC.ts()).allMatch((x,y) -> eqModXRC(bs, x, y));
  }
  private static T withRC(T t, RC rc){ return t.withRC(rc); }
  private static T readImm(T t){ return t.readImm(); }
}
