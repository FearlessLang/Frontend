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
  static List<inferenceGrammarB.Declaration> parsePackage(SourceOracle o,boolean infer){
    return new ParsePackage()
      .of(List.of(),o.allFiles(),o,DbgBlock.dbg(),infer);
  }
  static void ok(String expected, String head, List<String> input, boolean infer){
    var o= oracle("p",head,input);
    var res= printError(()->parsePackage(o,infer),o);
    var got= res.stream()
      .map(Object::toString)
      .collect(Collectors.joining("\n"))+"\n";
    Err.strCmp(expected,got);
  }
  static void ok(String expected, String head, List<String> input){ ok(expected,head,input,false); }
  static void ok(String expected, List<String> input){ ok(expected,"role app000;",input); }
    
  static void fail(String expected, String head, List<String> input, boolean infer){
    var o= oracle("p",head,input);
    FearlessException fe= assertThrows(FearlessException.class, ()->parsePackage(o,infer));
    var got= fe.render(o);
    Err.strCmp(expected,got);
  }
    static void fail(String expected, String head, List<String> input){ fail(expected,head,input,false); }
    static void failI(String expected, String head, List<String> input){ fail(expected,head,input,true); }
  static void fail(String expected, List<String> input){ fail(expected,"role app000;",input); }

  //TODO: role? should be inferred as app000 if none? now there is an error.
  //if we keep it, test for the error.
@Test void base(){ok("""
p.A:{'this}
""","""
role app000;
""",List.of("""
A:{}
"""));}
@Test void same(){fail("""
In file: [###]/in_memory0.fear

002| B:{}
   | ^^

While inspecting a type name
Name clash: name "B" is declared in package p.
Name "B" is also used in a "use" directive.
Error 9  WellFormedness
""","""
role app000;
use base.Block as B;
""",List.of("""
B:{}
"""));}
@Test void meth(){ok("""
p.A:{'this .foo:p.A@p.A;->p.A:?;}
""",List.of("""
A:{ .foo:A-> A}
"""));}

@Test void decls_crossRef_param_and_return(){ ok("""
p.A:{'this .id:p.A@p.A;->p.A:?;}
p.C:{'this}
""",List.of(
"A:{ .id:A->A }",
"C:{}"));}

@Test void error_unknown_name_in_sig_param(){fail(
"""
In file: [###]/in_memory0.fear

002| A:{ .f:Z->A }
   |        ^^

While inspecting a type name
Undeclared name: name "Z" is not declared in package p.
Error 9  WellFormedness
""",List.of(
"A:{ .f:Z->A }"));}

@Test void use_alias_happy_path(){ok(
"""
p.A:{'this .m:base.Void@p.A;->base.Void:?;}
""","role app000;\nuse base.Void as D;\n",List.of(
"A:{ .m:D->D }"));}

@Test void use_alias_clash_with_declared(){fail(
"""
In file: [###]/in_memory0.fear

002| D:{}
   | ^^

While inspecting a type name
Name clash: name "D" is declared in package p.
Name "D" is also used in a "use" directive.
Error 9  WellFormedness
""",
"role app000;\nuse base.Void as D;\n",List.of(
"D:{}"));}

@Test void round_elimination_in_simple_positions(){ok(
"p.A:{'this .id:p.A@p.A;->p.A:?;}",
"role app000;\n",List.of(
"A:{ .id:A->((A)) }"));}

@Test void extract_multiple_sigs_no_impls(){ok(
"""
p.A:{'this\
 .a:p.A@p.A;->p.A:?;\
 .b:p.A@p.A;->p.A:?;\
 .c:p.A@p.A;->p.A:?;}
""",
List.of("A:{ .a:A->A; .b:A->A; .c:A->A; }"));}

@Test void visitCall_base(){fail("""
In file: [###]/in_memory0.fear

002| A:{ .id:A->A; .id[X](x:A):A->x; .use:A->A; .use(x:A)->x.id(); }
   |                                            ^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "A"
Can not infer return type of method ".use(p.A):?".
No supertype has a method named ".use" with 1 parameters.
Error 9  WellFormedness
""",
"role app000;\n", List.of(
"A:{ .id:A->A; .id[X](x:A):A->x; .use:A->A; .use(x:A)->x.id(); }"));}

@Test void visitCall_base_ok(){ok("""
p.A:{'this\
 .id:p.A@p.A;->p.A:?;\
 .id[X:imm](p.A):p.A@p.A;(x)->x:?;\
 .use:p.A@p.A;->p.A:?;\
 .use(p.A):p.A@p.A;(x)->x:?.id():?;}
""",
"role app000;\n", List.of(
"A:{ .id:A->A; .id[X](x:A):A->x; .use:A->A; .use(x:A):A->x.id(); }"));}

@Test void use_alias_shadows_local_used_name(){fail("""
In file: [###]/in_memory0.fear

002| A:{}
   | ^^

While inspecting a type name
Name clash: name "A" is declared in package p.
Name "A" is also used in a "use" directive.
Error 9  WellFormedness
""",
"role app000;\nuse base.Void as A;\n",List.of(
"A:{}", 
"C:{ .f:A->A }"));} // ambiguous A: local and alias

@Test void error_refers_to_alias_without_use_decl(){fail("""
In file: [###]/in_memory0.fear

002| A:{ .m:D->D }
   |        ^^

While inspecting a type name
Undeclared name: name "D" is not declared in package p.
Error 9  WellFormedness
""","role app000;\n",List.of(
"A:{ .m:D->D }"));}

@Test void duplicate_decl_same_name(){fail("""
In file: [###]/in_memory0.fear

002| B:{} A:{}
   |      ^^

While inspecting a type name
Duplicate type declaration for "A".
Error 9  WellFormedness
""","role app000;\n",List.of(
"B:{} A:{}","A:{}"));}
@Test void duplicate_decl_same_name_nested(){fail("""
In file: [###]/in_memory0.fear

002| B:{.foo:A-> A:{} }
   |             ^^

While inspecting a type name
Duplicate type declaration for "A".
Error 9  WellFormedness
""","role app000;\n",List.of(
"B:{.foo:A-> A:{} }","A:{}"));}

@Test void opt_explicit(){ok("""
p.Opt[T:imm]:{'this\
 .match[R:imm](p.OptMatch[T,R]):R@p.Opt;(m)->m:?.empty():?;}
p.OptMatch[T:imm, R:imm]:{'this\
 .empty:R@p.OptMatch;\
 .some(T):R@p.OptMatch;}
p.Opts:{'this\
 #[T:imm](T):p.Opt[T]@p.Opts;(t)->p.Some[T:imm]:p.Opt[T]{'_\
 ? .match[?](?):?@!;\
 .match(m)->m:?.some(t:?):?;}:?;}
p.Some[T:imm]:p.Opt[T]{'_\
 .match[R:imm](p.OptMatch[T,R]):R@p.Some;(m)->m:?.some(t:?):?;}
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
p.Opt[T:imm]:{'this\
 .match[R:imm](p.OptMatch[T,R]):R@p.Opt;(m)->m:?.empty():?;}
p.OptMatch[T:imm, R:imm]:{'this\
 .empty:R@p.OptMatch; .some(T):R@p.OptMatch;}
p.Opts:{'this\
 #[T:imm](T):p.Opt[T]@p.Opts;\
(t)->p.A_Opts:$?{'_ ? .match[?](?):?@!;\
 .match(m)->m:?.some(t:?):?;}:?;}
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
p.A:{'this .a[R:imm](p.F[R]):R@p.A;(f)->f:?#():?;}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this\
 .use:p.User@p.User;\
->p.A:?.a(p.A_User:$?{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
""",List.of("""
F[R]:{#:R}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a{User}}
"""));}
@Test void base_typed_literal_inference_0(){ok("""
p.A:{'this .a[R:imm](p.F[R]):R@p.A;(f)->f:?#():?;}
p.A_F:p.F[p.User]{'_ #:p.User@p.A_F;->p.User:?;}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this .use:p.User@p.User;->p.A:?.a(\
p.A_F:p.F[p.User]{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
""",List.of("""
F[R]:{#:R}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}
@Test void base_typed_literal_inference_freshClash1(){ok("""
p.A:{'this .a[R:imm](p.F[R]):R@p.A;(f)->f:?#():?;}
p.A_F:{'this}
p.C_F:p.F[p.User]{'_ #:p.User@p.C_F;->p.User:?;}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this\
 .use:p.User@p.User;->p.A:?.a(\
p.C_F:p.F[p.User]{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
""","role app000;\nuse base.Void as B_F;\n",List.of("""
F[R]:{#:R}
A_F:{}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}

@Test void base_typed_literal_inference_freshClash2(){ok("""
p.A:{'this .a[R:imm](p.F[R]):R@p.A;(f)->f:?#():?;}
p.B_F:{'this}
p.C_F:p.F[p.User]{'_ #:p.User@p.C_F;->p.User:?;}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this\
 .use:p.User@p.User;->p.A:?.a(\
p.C_F:p.F[p.User]{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
""","role app000;\nuse base.Void as A_F;\n",List.of("""
F[R]:{#:R}
B_F:{}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}
@Test void importImpl(){ok("""
p.A:p.B, p.C{'this}
p.B:p.C{'this}
p.C:{'this}
""","role app000;\n",List.of("""
A:B{}
B:C{}
C:{}
"""));}
@Test void circular1(){fail("""
In file: [###]/in_memory0.fear

003| B:A{}
   |   ^^^

While inspecting type declarations
Circular implementation relation found involving "p.A".
Error 9  WellFormedness
""","role app000;\n",List.of("""
A:B{}
B:A{}
"""));}
@Test void circular2(){fail("""
In file: [###]/in_memory1.fear

002| B:A{}
   |   ^^^

While inspecting type declarations
Circular implementation relation found involving "p.A".
Error 9  WellFormedness
""","role app000;\n",List.of("""
A:B{}
""","""
B:A{}
"""));}
@Test void importSig(){ok("""
p.A:p.B, p.C{'this .foo:p.C@p.B;}
p.B:p.C{'this .foo:p.C@p.B;->p.C:?.foo():?;}
p.C:{'this .foo:p.C@p.C;}
""","role app000;\n",List.of("""
A:B{}
B:C{ .foo->C.foo}
C:{.foo:C;}
"""));}
@Test void implicit1(){ok("""
p.A:{'this #(p.A):p.A@p.A;}
p.B:p.A{'this #(p.A):p.A@p.B;(a_impl)->a_impl:?;}
p.C:p.A{'this #(p.A):p.A@p.C;(a_impl)->a_impl:?#(a_impl:?):?;}
p.D:p.A{'this #(p.A):p.A@p.D;(a_impl)->a_impl:?#():?#():?;}
""",List.of("""
A:{ #(x:A):A }
B:A{::}
C:A{::#::}
D:A{::# #}
"""));}

@Test void implicit2(){ok("""
p.A:{'this #(p.A):p.A@p.A; #(p.A,p.A):p.A@p.A;}
p.B:p.A{'this #(p.A):p.A@p.B;(a_impl)->a_impl:?; #(p.A,p.A):p.A@p.A;}
p.C:p.A{'this #(p.A):p.A@p.C;(a_impl)->a_impl:?; #(p.A,p.A):p.A@p.C;(z, b_impl)->b_impl:?;}
p.D:p.A{'this #(p.A,p.A):p.A@p.D;(z, a_impl)->a_impl:?.bar(p.A_D:$?{'_ ? [?](?):?@!; (b_impl)->b_impl:?.foo(p.D:?):?;}:?):?; #(p.A):p.A@p.A;}
""",List.of("""
A:{ #(x:A):A; #(x:A,y:A):A }
B:A{::}
C:A{::; z->::}
D:A{z->::.bar {::.foo(D)}}
"""));}

@Test void baseBlock(){ok("""
[###]
""",List.of(DbgBlock.baseBody));}

@Test void baseLet(){ok("""
p.A:{'this\
 #:p.A@p.A;->base.Block:?#():?\
.let(\
p.A_A:$?{'_ ? [?]:?@!; ()->p.A:?;}:?,\
p.C_A:$?{'_ ? [?](?,?):?@!;\
 (x, a_eqS)->a_eqS:?\
.return(p.B_A:$?{'_ ? [?]:?@!; ()->x:?;}:?):?;}:?):?;}
""","role app000;use base.Block as Block;",List.of("""
A:{ #:A->Block#.let x={A}.return {x} }
"""));}

@Test void xpat1(){ok("""
p.A:{'this #(p.A):p.A@p.A;}
p.B:p.A{'this\
 #(p.A):p.A@p.B;\
(a_div)->base.Block:?#():?\
.let(p.A_B:$?{'_ ? [?]:?@!; ()->a_div:?\
.a():?.b():?;}:?,\
p.B_B:$?{'_ ? [?](?,?):?@!;\
 (b3, b_eqS)->b_eqS:?;}:?):?\
.let(p.C_B:$?{'_ ? [?]:?@!;\
 ()->a_div:?.c():?.d():?;}:?,\
p.D_B:$?{'_ ? [?](?,?):?@!;\
 (d3, a_eqS)->a_eqS:?;}:?):?\
.return(p.E_B:$?{'_ ? [?]:?@!;\
 ()->b3:?+(d3:?):?;}:?):?;}
""",List.of("""
A:{ #(A):A }
B:A{ #{.a.b,.c.d}3->b3+d3 }
"""));}

@Test void eqDeep(){ok("""
p.A:{'this .bar(p.A):p.A@p.A;}
p.B:p.A{'this\
 .bar(p.A):p.A@p.B;(a_impl)->a_impl:?\
.foo():?.let(\
base.1:?,\
p.B_B:$?{'_ ? [?](?,?):?@!;\
 (x, a_eqS)->a_eqS:?.bla(base.2:?):?\
.let(base.3:?,p.A_B:$?{'_ ? [?](?,?):?@!;\
 (y, b_eqS)->b_eqS:?.beer(base.4:?):?;}:?):?;}:?):?;}
""",List.of("""
A:{ .bar(A):A}
B:A{ ::.foo.let x=1 .bla 2 .let y= 3 .beer 4}
"""));}

@Test void eqImplicit(){ok("""
p.A:{'this .bar(p.A):p.A@p.A;}
p.B:p.A{'this\
 .bar(p.A):p.A@p.B;(a_impl)->a_impl:?.foo():?.let(\
a_impl:?,p.B_B:$?{'_\
 ? [?](?,?):?@!;\
 (x, a_eqS)->a_eqS:?.bla(a_impl:?):?.let(\
a_impl:?,p.A_B:$?{'_\
 ? [?](?,?):?@!;\
 (y, b_eqS)->b_eqS:?.beer(a_impl:?):?;}:?):?;}:?):?;}
""",List.of("""
A:{ .bar(A):A}
B:A{ ::.foo.let x=:: .bla :: .let y= :: .beer ::}
"""));}

@Test void strLit1(){ok("""
p.A:{'this\
 .foo:p.A@p.A;->base.SStrProcs:?\
.add(base.` foo `:?,p.A:?):?.build(base.` bar
 beer
`:?):?;}
""",List.of("""
A:{ .foo:A -> 
  #|` foo {A} bar
  #|` beer
}
"""));}
@Test void strLit2(){ok("""
p.A:{'this\
 .foo:p.A@p.A;->base.UStrProcs:?\
.add(base." foo ":?,p.A:?):?\
.build(base." bar
 beer
":?):?;}
""",List.of("""
A:{ .foo:A -> 
  #|" foo {A} bar
  #|" beer
}
"""));}
@Test void strLit3(){ok("""
p.A:{'this\
 .foo:p.A@p.A;->p.A:?\
.foo(base.UStrProcs:?\
.add(base." foo ":?,p.A:?):?\
.build(base." bar
 beer
":?):?):?;}
""",List.of("""
A:{ .foo:A -> A.foo(
  #|" foo {A} bar
  #|" beer
)}
"""));}
@Test void strLit4(){ok("""
p.A:{'this\
 .foo:p.A@p.A;->p.A:?\
.foo(base.UStrProcs:?\
.add(base." foo ":?,p.A:?):?\
.build(base." bar
 beer
":?):?):?;}
""",List.of("""
A:{ .foo:A -> A.foo
  #|" foo {A} bar
  #|" beer
}
"""));}
@Test void rcAgreement1(){ok("""
p.A1:{'this .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A1@p.A2;}
p.B:p.A1, p.A2{'this .foo:p.A1@p.B;->p.A1:?;}
""",List.of("""
A1:{ imm .foo:A1;}
A2:{ .foo:A1;}
B:A1,A2{ .foo->A1 }
"""));}

@Test void rcAgreement2(){ok("""
p.A1:{'this .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A1@p.A2;}
p.B:p.A1, p.A2{'this .foo:p.A1@p.B;}
""",List.of("""
A1:{ imm .foo:A1;}
A2:{ .foo:A1;}
B:A1,A2{ }
"""));}

@Test void retDisagreement1(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ }
   | ^^^^^^^^^^

While inspecting type declaration "B"
Return type disagreement for method ".foo" with 0 parameters.
Different options are present in the implemented types: "p.A1", "p.A2".
Type "p.B" must declare a method ".foo" explicitly chosing the desired option.
Error 9  WellFormedness""",List.of("""
A1:{ .foo:A1;}
A2:{ .foo:A2;}
B:A1,A2{ }
"""));}
@Test void retDisagreement2(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ .foo->this.foo}
   |          ^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Return type disagreement for method ".foo" with 0 parameters.
Different options are present in the implemented types: "p.A1", "p.A2".
Type "p.B" must declare a method ".foo" explicitly chosing the desired option.
Error 9  WellFormedness""",List.of("""
A1:{ .foo:A1;}
A2:{ .foo:A2;}
B:A1,A2{ .foo->this.foo}
"""));}
@Test void parTDisagreement1(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ }
   | ^^^^^^^^^^

While inspecting type declaration "B"
Type disagreement about argument 1 for method ".foo" with 2 parameters.
Different options are present in the implemented types: "p.A1", "p.A2".
Type "p.B" must declare a method ".foo" explicitly chosing the desired option.
Error 9  WellFormedness""",List.of("""
A1:{ .foo(a:A1,b:A1):A1;}
A2:{ .foo(a:A1,b:A2):A1;}
B:A1,A2{ }
"""));}
@Test void parTDisagreement2(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ .foo(a,b)->this.foo}
   |          ^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Type disagreement about argument 1 for method ".foo" with 2 parameters.
Different options are present in the implemented types: "p.A1", "p.A2".
Type "p.B" must declare a method ".foo" explicitly chosing the desired option.
Error 9  WellFormedness""",List.of("""
A1:{ .foo(a:A1,b:A1):A1;}
A2:{ .foo(a:A1,b:A2):A1;}
B:A1,A2{ .foo(a,b)->this.foo}
"""));}
@Test void boundDisagreement1(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
Number of generic type parameters disagreement for method ".foo" with 0 parameters.
Different options are present in the implemented types: "[X:imm]", "[]".
Type "p.B" must declare a method ".foo" explicitly chosing the desired option.
Error 9  WellFormedness""",List.of("""
A1:{ .foo[X:imm]():A1;}
A2:{ .foo():A1;}
B:A1,A2{}
"""));}
@Test void boundDisagreement2(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ .foo()->this.foo }
   |          ^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
Number of generic type parameters disagreement for method ".foo" with 0 parameters.
Different options are present in the implemented types: "[X:imm]", "[]".
Type "p.B" must declare a method ".foo" explicitly chosing the desired option.
Error 9  WellFormedness""",List.of("""
A1:{ .foo[X:imm]():A1;}
A2:{ .foo():A1;}
B:A1,A2{ .foo()->this.foo }
"""));}
@Test void boundDisagreement3(){ok("""
p.A1:{'this .foo[X:imm]:p.A1@p.A1;}
p.A2:{'this .foo[Y:imm]:p.A1@p.A2;}
p.B:p.A1, p.A2{'this .foo[X:imm]:p.A1@p.B;->this:?.foo():?;}
""",List.of("""
A1:{ .foo[X:imm]():A1;}
A2:{ .foo[Y:imm]():A1;}
B:A1,A2{ .foo()->this.foo }
"""));}
@Test void boundAgreementAlpha(){ok("""
p.A1:{'this .foo[X:imm]:p.A1@p.A1;}
p.A2:{'this .foo[X:imm]:p.A1@p.A2;}
p.B[X:imm]:p.A1, p.A2{'this\
 .foo[A_X:imm]:p.A1@p.B;->this:?.foo():?;}
""",List.of("""
A1:{ .foo[X:imm]():A1;}
A2:{ .foo[X:imm]():A1;}
B[X:imm]:A1,A2{ .foo()->this.foo }
"""));}
@Test void ambigMethName1(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ this.foo }
   |          ^^^^^^^^^^

While inspecting type declaration "B"
Can not infer the name for method with 0 parameters.
Many abstract methods with 0 parameters could be selected:
Candidates: "imm .foo", "imm .bar".
Error 9  WellFormedness
""",List.of("""
A1:{ .foo():A1; .baz(x:A1):A1->this.baz(x); .beer(x:A1):A1->this.foo; }
A2:{ .bar():A1; .baz:A1->this.baz}
B:A1,A2{ this.foo }
"""));}
@Test void ambigMethName2(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ y->this.foo }
   |          ^^^^^^^^^^^^^

While inspecting type declaration "B"
Can not infer the name for method with 1 parameters.
Many methods with 1 parameters could be selected:
Candidates: "imm .baz", "imm .beer".
Error 9  WellFormedness
""",List.of("""
A1:{ .foo():A1; .baz(x:A1):A1->this.baz(x); .beer(x:A1):A1->this.foo; }
A2:{ .bar():A1; .baz:A1->this.baz}
B:A1,A2{ y->this.foo }
"""));}

@Test void diamondOk(){ok("""
p.A1:{'this .foo:p.A1@p.A1;->this:?;}
p.A2:p.A1{'this .foo:p.A1@p.A1;}
p.A3:p.A1{'this .foo:p.A1@p.A1;}
p.B:p.A1, p.A2, p.A3{'this .foo:p.A1@p.A1;}
""",List.of("""
A1:{ .foo():A1->this;}
A2:A1{ }
A3:A1{ }
B:A2,A3{ }
"""));}

@Test void diamondBad1(){fail("""
In file: [###]/in_memory0.fear

005| B:A2,A3{ }
   | ^^^^^^^^^^

While inspecting type declaration "B"
Ambiguos implementation for method ".foo" with 0 parameters.
Different options are present in the implemented types: 
Candidates: "p.A2", "p.A1".
Type "p.B" must declare a method ".foo" explicitly implementing the desired behaviour.
Error 9  WellFormedness
""",List.of("""
A1:{ .foo():A1->this;}
A2:A1{ .foo->this; }
A3:A1{ }
B:A2,A3{ }
"""));}

@Test void diamondBad2(){fail("""
In file: [###]/in_memory0.fear

005| B:A2,A3{ }
   | ^^^^^^^^^^

While inspecting type declaration "B"
Ambiguos implementation for method ".foo" with 0 parameters.
Different options are present in the implemented types: 
Candidates: "p.A2", "p.A3".
Type "p.B" must declare a method ".foo" explicitly implementing the desired behaviour.
Error 9  WellFormedness
""",List.of("""
A1:{ .foo():A1->this;}
A2:A1{ .foo->this; }
A3:A1{ .foo->this; }
B:A2,A3{ }
"""));}

@Test void badUppercaseRole(){fail("""
In file: [###]/p.fear

001| package p;
002| role App000;
   | -----^^^^^^

While inspecting header element > file header > full file
Missing "role" keyword.
Found instead: "App000".
Expected: " one of: base, core, driver, worker, framework, accumulator, tool, app followed by rank (eg. core023, app000, framework999)".
Error 2  UnexpectedToken
""","role App000;",List.of("""
B:{ }
"""));}

@Test void undefinedUse(){fail("""
In file: [###]/p.fear

002| role app000; use base.AAAA as BBB;
   |                  ^^^^^^^^^

While inspecting package header
"use" directive referes to undeclared name: name "AAAA" is not declared in package base.
Error 9  WellFormedness
""","role app000; use base.AAAA as BBB;",List.of("""
B:{ }
"""));}
@Test void rcOverloadingOk1(){ok("""
p.A1:{'this .foo:p.A1@p.A1;}
p.A2:{'this mut .foo:p.A2@p.A2;}
p.B:p.A1, p.A2{'this\
 .foo:p.A1@p.B;->p.B:?;\
 mut .foo:p.A2@p.B;->p.B:?;}
""",List.of("""
A1:{ imm .foo():A1; }
A2:{ mut .foo():A2; }
B:A1,A2{ .foo->B; }
"""));}

@Test void rcOverloadingOk2(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ A1 }
   |          ^^^^

While inspecting type declaration "B"
Can not infer the name for method with 0 parameters.
Many abstract methods with 0 parameters could be selected:
Candidates: "mut .foo", "imm .foo".
Error 9  WellFormedness
""",List.of("""
A1:{ mut .foo:A1;}
A2:{ imm .foo:A1;}
B:A1,A2{ A1 }
"""));}

@Test void rcOverloadingOk3(){ok("""
p.A1:{'this mut .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A2@p.A2;}
p.B:p.A1, p.A2{'this\
 mut .foo:p.A1@p.B;\
 .foo:p.A2@p.B;}
""",List.of("""
A1:{ mut .foo:A1;}
A2:{ imm .foo:A2;}
B:A1,A2{ mut .foo:A1; imm .foo:A2; }
"""));}

@Test void rcOverloadingOk4(){ok("""
p.A1:{'this mut .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A2@p.A2;}
p.B:p.A1, p.A2{'this\
 mut .foo:p.A1@p.A1;\
 .foo:p.A2@p.A2;}
""",List.of("""
A1:{ mut .foo:A1;}
A2:{ imm .foo:A2;}
B:A1,A2{ }
"""));}

@Test void rcOverlaoad1(){ok("""
p.A1:{'this mut .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A1@p.A2;}
p.B:p.A1, p.A2{'this mut .foo:p.A1@p.A1; .foo:p.A1@p.A2;}
""",List.of("""
A1:{ mut .foo:A1;}
A2:{ imm .foo:A1;}
B:A1,A2{ }
"""));}
@Test void rcOverlaoad2(){ok("""
p.A1:{'this mut .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A1@p.A2;}
p.B:p.A1, p.A2{'this mut .foo:p.A1@p.A1; .foo:p.A1@p.A2;}
""",List.of("""
A1:{ mut .foo:A1;}
A2:{ .foo:A1;}
B:A1,A2{ }
"""));}
@Test void inferMini3Err(){fail("""
In file: [###]/in_memory0.fear

004|   .foo[X](x:X,f:F[X,X]):X->f#x;
   |                 ^^

While inspecting a type name
Name: "F" is not declared with arity 2 in package p.
Did you accidentally add/omit a generic type parameter?
Error 9  WellFormedness
""",List.of("""
F:{#[A,B](A):B}
User:{
  .foo[X](x:X,f:F[X,X]):X->f#x;
  .bar->this.foo(User,{::})
  }
"""));}

}
//TODO: in the guide somewhere show #|" foo{#U+`AB02`} for arbitrary Unicode
