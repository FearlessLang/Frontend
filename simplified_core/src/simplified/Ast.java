package simplified;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import utils.Join;
import utils.Streams;

final class Fail extends RuntimeException{
  private static final long serialVersionUID= 1L;
  Fail(String msg){ super(msg); }
}
sealed interface T{
  T u= new U();
  record U() implements T{ @Override public String toString(){ return "?"; } }
  record X(String name) implements T{ @Override public String toString(){ return name; } }
  record C(String name, List<T> ts) implements T{ @Override public String toString(){ return name+Join.of(ts, "[", ",", "]", ""); } }
  static List<T> xs(List<String> xs){ return xs.stream().<T>map(X::new).toList(); }
  static Map<String,T> map(List<String> xs, List<T> ts){
    var res= new HashMap<String,T>();
    Streams.zip(xs, ts).forEach(res::put);
    return res;
  }
  default boolean settled(){ return switch (this){
    case U _ -> false;
    case X _ -> true;
    case C(_, var ts) -> ts.stream().allMatch(T::settled);
  };}
  default boolean has(String x){ return switch (this){
    case U _ -> false;
    case X(var n) -> n.equals(x);
    case C(_, var ts) -> ts.stream().anyMatch(t -> t.has(x));
  };}
  default T subst(Map<String,T> s){ return switch (this){
    case U _ -> this;
    case X(var n) -> s.getOrDefault(n, this);
    case C(var n, var ts) -> new C(n, ts.stream().map(t -> t.subst(s)).toList());
  };}
  default T fill(T info){
    if (this instanceof U){ return info; }
    if (!(this instanceof C(var n, var ts) && info instanceof C(var n2, var ts2) && n.equals(n2))){ return this; }
    return new C(n, Streams.zip(ts, ts2).map(T::fill).toList());
  }
  default boolean compatible(T info){
    if (this instanceof U || info instanceof U){ return true; }
    if (!(this instanceof C(var n, var ts) && info instanceof C(var n2, var ts2))){ return equals(info); }
    return n.equals(n2) && Streams.zip(ts, ts2).allMatch(T::compatible);
  }
}
sealed interface E{
  record X(String name, T t) implements E{ @Override public String toString(){ return name; } }
  record Call(E e, String m, Optional<List<T>> targs, List<E> es) implements E{
    @Override public String toString(){ return e+"."+m+targs.map(ts -> Join.of(ts, "[", ",", "]", "")).orElse("")+Join.of(es, "(", ",", ")", "()"); }
  }
  record L(String name, List<String> xs, List<T> ts, List<M> ms, T t) implements E{
    boolean anon(){ return name.isEmpty(); }
    T self(){ return anon() ? (ts.isEmpty() ? T.u : ts.getFirst()) : new T.C(name, T.xs(xs)); }
    @Override public String toString(){
      var head= anon() && ts.isEmpty() ? "" : (anon() ? "_" : name+Join.of(xs, "[", ",", "]", ""))+":"+Join.of(ts, "", ",", "", "");
      return head+Join.of(ms, "{", "", "}", "{}");
    }
  }
}
record M(String name, List<String> xs, List<String> ps, List<T> ts, T ret, Optional<E> e){
  M subst(Map<String,T> s){ return new M(name, xs, ps, ts.stream().map(t -> t.subst(s)).toList(), ret.subst(s), e); }
  M rename(List<String> to){ return new M(name, to, ps, ts, ret, e).subst(T.map(xs, T.xs(to))); }
  M fill(M info){ return new M(name, xs, ps, Streams.zip(ts, info.ts).map(T::fill).toList(), ret.fill(info.ret), e); }
  boolean settled(){ return ret.settled() && ts.stream().allMatch(T::settled); }
  @Override public String toString(){
    var sig= name+Join.of(xs, "[", ",", "]", "")+Join.of(Streams.zip(ps, ts).map((p, t) -> p+":"+t), "(", ",", ")", "()")+":"+ret;
    return sig+e.map(b -> "->"+b).orElse("")+";";
  }
}
