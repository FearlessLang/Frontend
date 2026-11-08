package fuzz;

import static java.lang.annotation.ElementType.TYPE_USE;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;
import java.lang.reflect.AnnotatedParameterizedType;
import java.lang.reflect.AnnotatedType;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.List;
import java.util.Random;
import java.util.stream.IntStream;
import java.util.stream.Stream;

final class Gen{
  @Retention(RUNTIME) @Target(TYPE_USE) @interface Size{ int min() default 0; int max(); }
  @Retention(RUNTIME) @Target(TYPE_USE) @interface OneOf{ String[] value(); }
  final Random r;
  final int maxDepth;
  int depth= 0;
  Gen(Random r, int maxDepth){ this.r= r; this.maxDepth= maxDepth; }
  <T> T of(Class<T> c){ return c.cast(value(c, c)); }
  Object value(AnnotatedType at){ return value(at.getType(), at); }
  Object value(Type t, java.lang.reflect.AnnotatedElement at){
    if (at instanceof AnnotatedParameterizedType p){
      var s= p.getAnnotation(Size.class);
      return IntStream.range(0, s.min()+r.nextInt(s.max()-s.min()+1)).mapToObj(_ -> value(p.getAnnotatedActualTypeArguments()[0])).toList();
    }
    var c= (Class<?>)t;
    if (c == String.class){ return pick(List.of(at.getAnnotation(OneOf.class).value())); }
    if (c == boolean.class){ return r.nextBoolean(); }
    if (c.isEnum()){ return pick(List.of(c.getEnumConstants())); }
    if (!c.isSealed()){ return record(c); }
    return record(pick(depth < maxDepth ? List.of(c.getPermittedSubclasses()) : leaves(c)));
  }
  <T> T pick(List<T> ts){ return ts.get(r.nextInt(ts.size())); }
  Object record(Class<?> c){
    var cs= c.getRecordComponents();
    depth += 1;
    try{
      var args= Stream.of(cs).map(rc -> value(rc.getAnnotatedType())).toArray();
      return c.getDeclaredConstructor(Stream.of(cs).map(RecordComponent::getType).toArray(Class[]::new)).newInstance(args);
    }
    catch (ReflectiveOperationException e){ throw new Error(e); }
    finally{ depth -= 1; }
  }
  static List<Class<?>> leaves(Class<?> sealed){ return Stream.of(sealed.getPermittedSubclasses()).filter(Gen::leaf).toList(); }
  static boolean leaf(Class<?> c){ return Stream.of(c.getRecordComponents()).noneMatch(rc -> recursive(rc.getGenericType())); }
  static boolean recursive(Type t){
    if (t instanceof ParameterizedType p){ return recursive(p.getActualTypeArguments()[0]); }
    return t instanceof Class<?> c && (c.isSealed() || c.isRecord() && !leaf(c));
  }
}
