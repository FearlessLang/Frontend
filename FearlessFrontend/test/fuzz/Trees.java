package fuzz;

import java.lang.reflect.AnnotatedParameterizedType;
import java.lang.reflect.AnnotatedType;
import java.lang.reflect.RecordComponent;
import java.util.List;
import java.util.function.BiFunction;
import java.util.stream.Stream;

final class Trees{
  static boolean position(AnnotatedType t){ return t != null; }
  static int positions(Object root){ return size(root, null); }
  static int size(Object v, AnnotatedType t){
    var here= position(t) ? 1 : 0;
    if (v instanceof List<?> l){ return here+l.stream().mapToInt(x -> size(x, element(t))).sum(); }
    if (!v.getClass().isRecord()){ return here; }
    return here+Stream.of(v.getClass().getRecordComponents()).mapToInt(c -> size(get(c, v), c.getAnnotatedType())).sum();
  }
  static Object replace(Object v, AnnotatedType t, int[] k, BiFunction<Object,AnnotatedType,Object> f){
    if (position(t) && k[0]-- == 0){ return f.apply(v, t); }
    if (v instanceof List<?> l){ return l.stream().map(x -> replace(x, element(t), k, f)).toList(); }
    if (!v.getClass().isRecord()){ return v; }
    var cs= v.getClass().getRecordComponents();
    var args= Stream.of(cs).map(c -> replace(get(c, v), c.getAnnotatedType(), k, f)).toArray();
    try{ return v.getClass().getDeclaredConstructor(Stream.of(cs).map(RecordComponent::getType).toArray(Class[]::new)).newInstance(args); }
    catch (ReflectiveOperationException e){ throw new Error(e); }
  }
  static <T> T replace(T root, int k, BiFunction<Object,AnnotatedType,Object> f){
    @SuppressWarnings("unchecked") var res= (T)replace(root, null, new int[]{k}, f);
    return res;
  }
  static AnnotatedType element(AnnotatedType t){ return ((AnnotatedParameterizedType)t).getAnnotatedActualTypeArguments()[0]; }
  static Object get(RecordComponent c, Object v){
    try{ return c.getAccessor().invoke(v); }
    catch (ReflectiveOperationException e){ throw new Error(e); }
  }
}
