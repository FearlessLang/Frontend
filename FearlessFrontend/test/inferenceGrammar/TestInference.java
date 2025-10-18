  /*static FileFull file(int i, String input, SourceOracle o){
    try{ return Parse.from(SourceOracle.defaultDbgUri(i), input); }
    catch(FearlessException fe){ System.out.println(fe.render(o)); throw fe; }
  }
  static List<FileFull> files(List<String> input){
    var o= oracle(input);
    return IntStream.range(0, input.size()).mapToObj(i->file(i,input.get(i),o)).toList();
  }*/

package inferenceGrammar;

import java.net.URI;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import fullWellFormedness.ParsePackage;
import message.FearlessException;
import message.SourceOracle;
import utils.Err;

public class TestInference {
  static SourceOracle oracle(String pkgName, String head, List<String> input){
    var o= SourceOracle.debugBuilder();
    o.put(pkgName+".fear", "package "+pkgName+";\n"+head);
    for(int i= 0; i < input.size(); i+=1){ o = o.put(i,"package "+pkgName+";\n"+input.get(i));}      
    return o.build();
  }
  static SourceOracle oracle(List<String> input){
    var o= SourceOracle.debugBuilder();
    for(int i= 0; i < input.size(); i+=1){ o = o.put(i,input.get(i));}
    return o.build();
  }
  static List<URI> filesUri(int size){
    return IntStream.range(0, size).mapToObj(SourceOracle::defaultDbgUri).toList();
  }
  static <R> R printError(Supplier<R> r, SourceOracle o){
    try{ return r.get(); }
    catch(FearlessException fe){ System.out.println(fe.render(o)); throw fe; }
  }
  static void ok(String expected, String head, List<String> input){
    var o= oracle("p",head,input);
    var res= printError(()->new ParsePackage().of(List.of(),o.allFiles(),o,0),o);
    var got= res.stream()
      .map(Object::toString)
      .collect(Collectors.joining("\n"))+"\n";
    Err.strCmp(expected,got);
  }
  static void ok(String expected, List<String> input){ ok(expected,"role app000;\nuse a.B as B;",input); }
  
  static void fail(String expected, String head, List<String> input){
    var o= oracle("p",head,input);
    FearlessException fe= assertThrows(FearlessException.class, ()->new ParsePackage().of(List.of(),o.allFiles(),o,0));
    var got= fe.render(o);
    Err.strCmp(expected,got);
  }
  static void fail(String expected, List<String> input){ fail(expected,"role app000;\nuse a.B as B;",input); }

  //TODO: role? should be inferred as app000 if none? now there is an error.
  //if we keep it, test for the error.
@Test void base(){ok("""
p.A[]:{`this}:?
""","""
role app000;
use a.B as B;
""",List.of("""
A:{}
"""));}
@Test void same(){fail("""
In file: [###]/in_memory0.fear

002| B:{}
   | ^^

While inspecting the file
Name clash: name "B" is declared in package p.
Name "B" is also used in a "use" directive.
Error 10  WellFormedness
""","""
role app000;
use a.B as B;
""",List.of("""
B:{}
"""));}
@Test void meth(){ok("""
p.A[]:{`this imm .foo:imm p.A[]; .foo()->imm p.A[]:?;}:?
""",List.of("""
A:{ .foo:A-> A}
"""));}

@Test void decls_crossRef_param_and_return(){ ok("""
p.C[]:{`this}:?
p.A[]:{`this imm .id:imm p.A[]; .id()->imm p.A[]:?;}:?
""",List.of(
"A:{ .id:A->A }",
"C:{}"));}

@Test void error_unknown_name_in_sig_param(){fail(
"""
In file: [###]/in_memory0.fear

002| A:{ .f:Z->A }
   |        ^^

While inspecting the file
Undeclared name: name "Z" is not declared in package p.
Error 10  WellFormedness
""",List.of(
"A:{ .f:Z->A }"));}

@Test void use_alias_happy_path(){ok(
"""
p.A[]:{`this imm .m:imm c.D[]; .m()->imm c.D[]:?;}:?
""","role app000;\nuse c.D as D;\n",List.of(
"A:{ .m:D->D }"));}

@Test void use_alias_clash_with_declared(){fail(
"""
In file: [###]/in_memory0.fear

002| D:{}
   | ^^

While inspecting the file
Name clash: name "D" is declared in package p.
Name "D" is also used in a "use" directive.
Error 10  WellFormedness
""",
"role app000;\nuse c.D as D;\n",List.of(
"D:{}"));}

@Test void round_elimination_in_simple_positions(){ok(
"p.A[]:{`this imm .id:imm p.A[]; .id()->imm p.A[]:?;}:?",
"role app000;\n",List.of(
"A:{ .id:A->((A)) }"));}

@Test void extract_multiple_sigs_no_impls(){ok(
"""
p.A[]:{`this\
 imm .a:imm p.A[];\
 .a()->imm p.A[]:?;\
 imm .b:imm p.A[];\
 .b()->imm p.A[]:?;\
 imm .c:imm p.A[];\
 .c()->imm p.A[]:?;\
}:?""",
List.of("A:{ .a:A->A; .b:A->A; .c:A->A; }"));}

@Test void visitCall_base(){ok("""
p.A[]:{`this\
 imm .id:imm p.A[];\
 .id()->imm p.A[]:?;\
 imm .id[X:imm](imm p.A[]):imm p.A[];\
 .id(x)->x:?;\
 imm .use:imm p.A[];\
 .use()->imm p.A[]:?;\
 .use(x)->x:?.id():?;\
}:?
""",
"role app000;\n", List.of(
"A:{ .id:A->A; .id[X](x:A):A->x; .use:A->A; .use(x:A)->x.id(); }"));}

@Test void use_alias_shadows_local_used_name(){fail("""
In file: [###]/in_memory0.fear

002| A:{}
   | ^^

While inspecting the file
Name clash: name "A" is declared in package p.
Name "A" is also used in a "use" directive.
Error 10  WellFormedness
""",
"role app000;\nuse extpkg.A as A;\n",List.of(
"A:{}", 
"C:{ .f:A->A }"));} // ambiguous A: local and alias

@Test void error_refers_to_alias_without_use_decl(){fail("""
In file: [###]/in_memory0.fear

002| A:{ .m:D->D }
   |        ^^

While inspecting the file
Undeclared name: name "D" is not declared in package p.
Error 10  WellFormedness
""","role app000;\n",List.of(
"A:{ .m:D->D }"));}

@Test void duplicate_decl_same_name(){fail("""
In file: [###]/in_memory0.fear

002| B:{} A:{}
   |      ^^

While inspecting the file
Duplicate type declaration for "A".
Error 10  WellFormedness
""","role app000;\n",List.of(
"B:{} A:{}","A:{}"));}
@Test void duplicate_decl_same_name_nested(){fail("""
In file: [###]/in_memory0.fear

002| B:{.foo:A-> A:{} }
   |             ^^

While inspecting the file
Duplicate type declaration for "A".
Error 10  WellFormedness
""","role app000;\n",List.of(
"B:{.foo:A-> A:{} }","A:{}"));}

@Test void opt_explicit(){ok("""
p.Opt[T:imm]:{`this\
 imm .match[R:imm](imm p.OptMatch[T,R]):R;\
 .match(m)->m:?.empty():?;\
}:?
p.OptMatch[T:imm, R:imm]:{`this\
 imm .empty:R; imm .some(T):R;\
}:?
p.Some[T:imm]:p.Opt[T]{`_\
 .match(m)->m:?.some(t:?):?;\
}:?
p.Opts[]:{`this\
 imm #[T:imm](T):imm p.Opt[T];\
 #(t)->imm p.Some[T]:?;\
}:?
""",List.of("""
Opt[T]: {
  .match[R](m: OptMatch[T,R]): R -> m.empty
  }
OptMatch[T,R]: {
  .empty: R;
  .some(t: T): R;
  }
Opts: {
  #[T](t: T): Opt[T] -> Some[T]:Opt[T]{ .match(m) -> m.some(t) }
  }
"""));}
@Test void opt_implicit(){ok("""
p.Opt[T:imm]:{`this\
 imm .match[R:imm](imm p.OptMatch[T,R]):R;\
 .match(m)->m:?.empty():?;\
}:?
p.OptMatch[T:imm, R:imm]:{`this\
 imm .empty:R; imm .some(T):R;\
}:?
p.Opts[]:{`this\
 imm #[T:imm](T):imm p.Opt[T];\
 #(t)->{`_\
 .match(m)->m:?.some(t:?):?;}:?;\
}:?
""",List.of("""
Opt[T]: {
  .match[R](m: OptMatch[T,R]): R -> m.empty
  }
OptMatch[T,R]: {
  .empty: R;
  .some(t: T): R;
  }
Opts: {
  #[T](t: T): Opt[T] -> { .match(m) -> m.some(t) }
  }
"""));}
@Test void base_literal_inference_0(){ok("""
p.F[R:imm]:{`this imm #:R;}:?
p.A[]:{`this imm .a[R:imm](imm p.F[R]):R; .a(f)->f:?#():?;}:?
p.User[]:{`this imm .use:imm p.User[]; .use()->imm p.A[]:?.a({`_ ()->imm p.User[]:?;}:?):?;}:?
""",List.of("""
F[R]:{#:R}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a{User}}
"""));}
@Test void base_typed_literal_inference_0(){ok("""
p.F[R:imm]:{`this imm #:R;}:?
p.A[]:{`this imm .a[R:imm](imm p.F[R]):R; .a(f)->f:?#():?;}:?
p.A_F[]:p.F[imm p.User[]]{`_ ()->imm p.User[]:?;}:?
p.User[]:{`this imm .use:imm p.User[]; .use()->imm p.A[]:?.a(imm p.A_F[]:?):?;}:?
""",List.of("""
F[R]:{#:R}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}
@Test void base_typed_literal_inference_freshClash1(){ok("""
p.F[R:imm]:{`this imm #:R;}:?
p.A_F[]:{`this}:?
p.A[]:{`this imm .a[R:imm](imm p.F[R]):R; .a(f)->f:?#():?;}:?
p.C_F[]:p.F[imm p.User[]]{`_ ()->imm p.User[]:?;}:?
p.User[]:{`this imm .use:imm p.User[]; .use()->imm p.A[]:?.a(imm p.C_F[]:?):?;}:?
""","role app000;\nuse c.D as B_F;\n",List.of("""
F[R]:{#:R}
A_F:{}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}

@Test void base_typed_literal_inference_freshClash2(){ok("""
p.F[R:imm]:{`this imm #:R;}:?
p.B_F[]:{`this}:?
p.A[]:{`this imm .a[R:imm](imm p.F[R]):R; .a(f)->f:?#():?;}:?
p.C_F[]:p.F[imm p.User[]]{`_ ()->imm p.User[]:?;}:?
p.User[]:{`this imm .use:imm p.User[]; .use()->imm p.A[]:?.a(imm p.C_F[]:?):?;}:?
""","role app000;\nuse c.D as A_F;\n",List.of("""
F[R]:{#:R}
B_F:{}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}

}