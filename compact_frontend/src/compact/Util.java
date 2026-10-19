package compact;
import java.util.*;
import java.util.function.*;
import java.util.stream.*;
final class Util{
  static IntStream range(int n){ return IntStream.range(0,n);}
  static<A,B> List<B> map(Collection<A> xs, Function<A,B> f){ return xs.stream().map(f).toList();}
  static<A,B> List<B> flat(Collection<A> xs, Function<A,Stream<B>> f){ return xs.stream().flatMap(f).toList();}
  static<A> List<A> filter(Collection<A> xs, Predicate<A> p){ return xs.stream().filter(p).toList();}
  static<A> boolean any(Collection<A> xs, Predicate<A> p){ return xs.stream().anyMatch(p);}
  static<A> boolean all(Collection<A> xs, Predicate<A> p){ return xs.stream().allMatch(p);}
  static<A> Optional<A> find(Collection<A> xs, Predicate<A> p){ return xs.stream().filter(p).findFirst();}
  static<K,V> Map<K,List<V>> group(Collection<V> xs, Function<V,K> f){ return xs.stream().collect(Collectors.groupingBy(f, LinkedHashMap::new,Collectors.toList())); }
  @SafeVarargs@SuppressWarnings("varargs") static<A> List<A> list(A... xs){ return List.of(xs);}
  static boolean dup(List<?> l){ return l.stream().distinct().count()< l.size();}
  static<V> List<V> push(List<V>a,List<V>b){ return Stream.concat(a.stream(), b.stream()).toList();}
  static<V> List<V> push(List<V>a,V b){ return Stream.concat(a.stream(), Stream.of(b)).toList();}
  static<V> List<V> push(V a,List<V>b){ return Stream.concat(Stream.of(a), b.stream()).toList();}
  static<A,B,R> List<R> zip(List<A> as,List<B> bs, BiFunction<A,B,R> f){ return range(as.size()).mapToObj(i -> f.apply(as.get(i), bs.get(i))).toList();}
  @SafeVarargs@SuppressWarnings("varargs") static<V> Stream<V> cat(Stream<V>... ss){ return Stream.of(ss).flatMap(s -> s);}
  static<T> List<T> same(List<T> original,List<T> candidate){
    if(candidate == original)return original; for(int i=0;i < original.size(); i++){ if(candidate.get(i)!= original.get(i)) return candidate;}
    return original;}
}
