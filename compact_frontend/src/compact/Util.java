package compact;
import java.util.*;
import java.util.function.*;
import java.util.stream.*;
final class Util{
  static IntStream range(int n){ return IntStream.range(0,n);}
  static<A,B> List<B> map(Collection<A> v, Function<A,B> f){ return v.stream().map(f).toList();}
  static<A,B> List<B> flat(Collection<A> v, Function<A,Stream<B>> f){ return v.stream().flatMap(f).toList();}
  static<A> List<A> filter(Collection<A> v, Predicate<A> p){ return v.stream().filter(p).toList();}
  static<A> boolean any(Collection<A> v, Predicate<A> p){ return v.stream().anyMatch(p);}
  static<A> boolean all(Collection<A> v, Predicate<A> p){ return v.stream().allMatch(p);}
  static<A> A find(Collection<A> v, Predicate<A> p){ return v.stream().filter(p).findFirst().orElse(null);}
  static<K,V> Map<K,List<V>> group(Collection<V> v, Function<V,K> f){ return v.stream().collect(Collectors.groupingBy(f, LinkedHashMap::new,Collectors.toList())); }
  @SafeVarargs@SuppressWarnings("varargs") static<A> List<A> list(A... v){ return List.of(v);}
  static boolean dup(List<?> l){ return l.stream().distinct().count()< l.size();}
  static<V> List<V> push(List<V>a,List<V>b){ return Stream.concat(a.stream(), b.stream()).toList();}
  static<V> List<V> push(List<V>a,V b){ return Stream.concat(a.stream(), Stream.of(b)).toList();}
  static<V> List<V> push(V a,List<V>b){ return Stream.concat(Stream.of(a), b.stream()).toList();}
  static<A,B,R> List<R> zip(List<A> as,List<B> b, BiFunction<A,B,R> f){ return range(as.size()).mapToObj(i -> f.apply(as.get(i), b.get(i))).toList();}
  @SafeVarargs@SuppressWarnings("varargs") static<V> Stream<V> cat(Stream<V>... ss){ return Stream.of(ss).flatMap(s -> s);}
}
