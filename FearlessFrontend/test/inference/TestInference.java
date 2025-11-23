package inference;

import java.net.URI;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import message.FearlessException;
import message.SourceOracle;
import pkgmerge.ParsePackage;
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
  static List<inferenceCore.Declaration> parsePackage(SourceOracle o,boolean infer){
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

@Test void base(){ok("""
p.A:{'this}
""","""
role app000;
""",List.of("""
A:{}
"""));}

@Test void baseInfer(){fail("""
In file: [###]/p.fear

001| package p;
   | ^

While inspecting the file
Missing role declaration in package head file.
Every package must declare its role: base, core, driver, worker, framework, accumulator, tool, or app.
The package head file is the file whose name matches the package name.
Add a top-level role line to that file. For example:
package myCoolGame;
role app999;
use base.Main as Main;
MyGame:Main{s->Debug#(`Hello world`)}

As a rule of thumb: final applications use appNNN; shared libraries often use workerNNN or frameworkNNN.
Error 9 WellFormedness
""","""
""",List.of("""
A:{}
"""));}


@Test void same(){fail("""
In file: [###]/in_memory0.fear

002| B:{}
   | ^^

While inspecting a type name
Name clash: name "B" is declared in package "p".
Name "B" is also used in a "use" directive.
Error 9 WellFormedness
""","""
role app000;
use base.Block as B;
""",List.of("""
B:{}
"""));}

@Test void manyHeads(){fail("""
In file: [###]/in_memory0.fear

001| package p;
   | ^

While inspecting the file
File is not the package head, but contains package head directives.
It should not contain any directives like maps, uses or role.
Found non-empty:
  - uses: use base.Void as Void
Error 9 WellFormedness
""","""
role app000;
use base.Block as B;
""",List.of("""
use base.Void as Void;
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
Type "Z" is not declared in package "p" and is not made visible via "use".
In scope: "A".
Error 9 WellFormedness
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
Name clash: name "D" is declared in package "p".
Name "D" is also used in a "use" directive.
Error 9 WellFormedness
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
Cannot infer return type of method ".use(p.A):?".
No supertype has a method named ".use" with 1 parameters.
Error 9 WellFormedness
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
Name clash: name "A" is declared in package "p".
Name "A" is also used in a "use" directive.
Error 9 WellFormedness
""",
"role app000;\nuse base.Void as A;\n",List.of(
"A:{}", 
"C:{ .f:A->A }"));} // ambiguous A: local and alias

@Test void error_refers_to_alias_without_use_decl(){fail("""
In file: [###]/in_memory0.fear

002| A:{ .m:D->D }
   |        ^^

While inspecting a type name
Type "D" is not declared in package "p" and is not made visible via "use".
In scope: "A".
Error 9 WellFormedness
""","role app000;\n",List.of(
"A:{ .m:D->D }"));}

@Test void duplicate_decl_same_name(){fail("""
In file: [###]/in_memory0.fear

002| B:{} A:{}
   |      ^^

While inspecting a type name
Duplicate type declaration for "A".
Error 9 WellFormedness
""","role app000;\n",List.of(
"B:{} A:{}","A:{}"));}
@Test void duplicate_decl_same_name_nested(){fail("""
In file: [###]/in_memory0.fear

002| B:{.foo:A-> A:{} }
   |             ^^

While inspecting a type name
Duplicate type declaration for "A".
Error 9 WellFormedness
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
p.A_User:p.F[p.User]{'_ #:p.User@p.A_User;->p.User:?;}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this\
 .use:p.User@p.User;\
->p.A:?.a(p.A_User:p.F[p.User]{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
""",List.of("""
F[R]:{#:R}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}
@Test void base_typed_literal_inference_freshClash1(){ok("""
p.A:{'this .a[R:imm](p.F[R]):R@p.A;(f)->f:?#():?;}
p.A_F:{'this}
p.A_User:p.F[p.User]{'_ #:p.User@p.A_User;->p.User:?;}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this\
 .use:p.User@p.User;\
->p.A:?.a(p.A_User:p.F[p.User]{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
""","role app000;\nuse base.Void as B_F;\n",List.of("""
F[R]:{#:R}
A_F:{}
A:{ .a[R](f:F[R]):R->f#; }
User:{ .use:User->A.a F[User]{User}}
"""));}

@Test void base_typed_literal_inference_freshClash2(){ok("""
p.A:{'this .a[R:imm](p.F[R]):R@p.A;(f)->f:?#():?;}
p.A_User:p.F[p.User]{'_ #:p.User@p.A_User;->p.User:?;}
p.B_F:{'this}
p.F[R:imm]:{'this #:R@p.F;}
p.User:{'this\
 .use:p.User@p.User;\
->p.A:?.a(p.A_User:p.F[p.User]{'_ ? [?]:?@!; ()->p.User:?;}:?):?;}
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
Error 9 WellFormedness
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
Error 9 WellFormedness
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
Type "p.B" must declare a method ".foo" explicitly choosing the desired option.
Error 9 WellFormedness""",List.of("""
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
Type "p.B" must declare a method ".foo" explicitly choosing the desired option.
Error 9 WellFormedness""",List.of("""
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
Type "p.B" must declare a method ".foo" explicitly choosing the desired option.
Error 9 WellFormedness""",List.of("""
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
Type "p.B" must declare a method ".foo" explicitly choosing the desired option.
Error 9 WellFormedness""",List.of("""
A1:{ .foo(a:A1,b:A1):A1;}
A2:{ .foo(a:A1,b:A2):A1;}
B:A1,A2{ .foo(a,b)->this.foo}
"""));}
@Test void boundDisagreement1(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{}
   | ^^^^^^^^^

While inspecting type declaration "B"
The number of generic type parameters disagrees for method ".foo" with 0 parameters.
Different options are present in the implemented types: "[X:imm]", "[]".
Type "p.B" cannot implement all of those types.
Error 9 WellFormedness
""",List.of("""
A1:{ .foo[X:imm]():A1;}
A2:{ .foo():A1;}
B:A1,A2{}
"""));}
@Test void boundDisagreement2(){fail("""
In file: [###]/in_memory0.fear

004| B:A1,A2{ .foo()->this.foo }
   |          ^^^^^^^^^^^^^^^^^^

While inspecting type declaration "B"
The number of generic type parameters disagrees for method ".foo" with 0 parameters.
Different options are present in the implemented types: "[X:imm]", "[]".
Type "p.B" cannot implement all of those types.
Error 9 WellFormedness
""",List.of("""
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
Cannot infer the name for method with 0 parameters.
Many abstract methods with 0 parameters could be selected:
Candidates: "imm .foo", "imm .bar".
Error 9 WellFormedness
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
Cannot infer the name for method with 1 parameters.
Many methods with 1 parameters could be selected:
Candidates: "imm .baz", "imm .beer".
Error 9 WellFormedness
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
Ambiguous implementation for method ".foo" with 0 parameters.
Different options are present in the implemented types: 
Candidates: "p.A2", "p.A1".
Type "p.B" must declare a method ".foo" explicitly implementing the desired behaviour.
Error 9 WellFormedness
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
Ambiguous implementation for method ".foo" with 0 parameters.
Different options are present in the implemented types: 
Candidates: "p.A2", "p.A3".
Type "p.B" must declare a method ".foo" explicitly implementing the desired behaviour.
Error 9 WellFormedness
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
Error 2 UnexpectedToken
""","role App000;",List.of("""
B:{ }
"""));}

@Test void undefinedUse(){fail("""
In file: [###]/p.fear

002| role app000; use base.AAAA as BBB;
   |                  ^^^^^^^^^

While inspecting package header
"use" directive refers to undeclared name: type "AAAA" is not declared in package "base".
Error 9 WellFormedness
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

@Test void rcOverloadingOk2(){ok("""
p.A1:{'this mut .foo:p.A1@p.A1;}
p.A2:{'this .foo:p.A1@p.A2;}
p.B:p.A1, p.A2{'this\
 mut .foo:p.A1@p.B;->p.A1:?;\
 .foo:p.A1@p.B;->p.A1:?;}
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
Name "F" is not declared with 2 generic parameter(s) in package "p".
Name "F" is only declared with 0 generic parameter(s).
Did you accidentally add or omit a generic type parameter?
Error 9 WellFormedness
""",List.of("""
F:{#[A,B](A):B}
User:{
  .foo[X](x:X,f:F[X,X]):X->f#x;
  .bar->this.foo(User,{::})
  }
"""));}

@Test void inferAlpha_MultiSuper_DifferentBounds_ShouldDisagree(){ fail("""
In file: [###]/in_memory0.fear

005| D:A,C{}
   | ^^^^^^^

While inspecting type declaration "D"
Generic bounds disagreement for method ".id" with 1 parameters.
Different options are present in the implemented types: "[X:imm]", "[Y:read]".
Type "p.D" must declare a method ".id" explicitly choosing the desired option.
Error 9 WellFormedness
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X:imm](x:Box[X]):X}
C:{.id[Y:read](y:Box[Y]):Y}
D:A,C{}
"""));}

@Test void inferAlpha_ArityMismatch_BetweenSupers_OrOverride(){ fail("""
In file: [###]/in_memory0.fear

003| E:A{.m[U](u:U,g:U):U} // mismatch on method generic arity and params
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "E"
Method ".m" declares 1 generic parameter(s), but supertypes declare 2.
Local declaration: "[U:imm]".
From supertypes: "[X:imm, Y:imm]".
Change the local number of generic parameters to 2, or adjust the supertypes.
Error 9 WellFormedness
""", List.of("""
A:{.m[X,Y](x:X,y:Y):X}
E:A{.m[U](u:U,g:U):U} // mismatch on method generic arity and params
"""));}

@Test void inferAlpha_ClassParamNameCollides_WithMethodParamName(){ fail("""
In file: [###]/in_memory0.fear

001| package p;
   | ... 2 lines ...
004| B[X]:A{.id[X](b:Box[X])->b.get} // class X vs method X
   | -------~~~~^~~~~~~~~~~~--------

While inspecting generic bounds declaration > method signature > method declaration > type declaration body > type declaration > full file
Name "X" already in scope.
Error 2 UnexpectedToken
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X](x:Box[X]):X}
B[X]:A{.id[X](b:Box[X])->b.get} // class X vs method X
"""));}

@Test void inferAlpha_MergeTwoSupers_SwappedOrder_NestedArgs(){ fail("""
In file: [###]/in_memory0.fear

006| D:A,C{}
   | ^^^^^^^

While inspecting type declaration "D"
Type disagreement about argument 0 for method ".m" with 1 parameters.
Different options are present in the implemented types: "p.Twice[p.Pair[X,Y]]", "p.Twice[p.Pair[Y,X]]".
Type "p.D" must declare a method ".m" explicitly choosing the desired option.
Error 9 WellFormedness
""", List.of("""
Pair[AA,BB]:{.fst:AA;.snd:BB;}
Twice[T]:{.get:Pair[T,T];}
A:{.m[X,Y](t:Twice[Pair[X,Y]]):X}
C:{.m[U,V](t:Twice[Pair[V,U]]):U}
D:A,C{}
"""));}

@Test void nested5a(){ok("""
p.A_User:p.GG{'_ .apply[F_A0:imm](F_A0):F_A0@p.A_User;(a2)->a2:?;}
p.B_User:p.GG{'_ .apply[C_A0:imm](C_A0):C_A0@p.B_User;(a4)->a4:?;}
p.C_User:p.GG{'_ .apply[A_A0:imm](A_A0):A_A0@p.C_User;(a3)->this:?.withGG(p.B_User:p.GG{'_ ? [?](?):?@!; (a4)->a4:?;}:?):?;}
p.D_User:p.GG{'_ .apply[B_A0:imm](B_A0):B_A0@p.D_User;(a5)->a5:?;}
p.E_User:p.GG{'_ .apply[D_A0:imm](D_A0):D_A0@p.E_User;(a4)->this:?.withGG(p.D_User:p.GG{'_ ? [?](?):?@!; (a5)->a5:?;}:?):?;}
p.F_User:p.GG{'_ .apply[E_A0:imm](E_A0):E_A0@p.F_User;(a3)->this:?.withGG(p.E_User:p.GG{'_ ? [?](?):?@!; (a4)->this:?.withGG(p.D_User:p.GG{'_ ? [?](?):?@!; (a5)->a5:?;}:?):?;}:?):?;}
p.GG:{'this .apply[A0:imm](A0):A0@p.GG;}
p.User:{'this .withGG(p.GG):p.User@p.User; .id1[A0:imm,A1:imm]:p.User@p.User;->this:?.withGG(p.A_User:p.GG{'_ ? [?](?):?@!; (a2)->a2:?;}:?):?; .id2[A0:imm,A1:imm]:p.User@p.User;->this:?.withGG(p.C_User:p.GG{'_ ? [?](?):?@!; (a3)->this:?.withGG(p.B_User:p.GG{'_ ? [?](?):?@!; (a4)->a4:?;}:?):?;}:?):?; .id3[A0:imm,A1:imm]:p.User@p.User;->this:?.withGG(p.F_User:p.GG{'_ ? [?](?):?@!; (a3)->this:?.withGG(p.E_User:p.GG{'_ ? [?](?):?@!; (a4)->this:?.withGG(p.D_User:p.GG{'_ ? [?](?):?@!; (a5)->a5:?;}:?):?;}:?):?;}:?):?;}
""", List.of("""
GG:{ .apply[A0](A0):A0 }
User:{
  .withGG(GG):User;
  .id1[A0,A1]:User->this.withGG GG{a2->a2};
  .id2[A0,A1]:User->this.withGG GG{a3->this.withGG GG{a4->a4}};
  .id3[A0,A1]:User->this.withGG GG{a3->this.withGG GG{a4->this.withGG GG{a5->a5}};
  }
}
"""));}

@Test void abcdBadK(){fail("""
In file: [###]/in_memory0.fear

008|   .foo2[C,D]:User->KK:{ .k[K]:K->this.withGG[C,D]({a,b,c->Any!})}.k[K];
   |                                                                     ^^

While inspecting a type name
Type "K" is not declared in package "p" and is not made visible via "use".
In scope: "Any", "Baba", "GG", "KK", "User".
Error 9 WellFormedness
""", List.of("""
GG[A,B]:{ .apply[C,D](A,B,C):D }
Baba[C,D]:GG[Any,Any]{}
Any:{![T]:T->Any![T]}
User:{
  .withGG[A1,B1](GG[A1,B1]):User;
  .foo1[C,D]:User->this.withGG[C,D]({a,b,c->Any!});
  .foo2[C,D]:User->KK:{ .k[K]:K->this.withGG[C,D]({a,b,c->Any!})}.k[K];
}
"""));}

@Test void inLineAnonObject1(){ok("""
p.Bla:{'_ .bla:p.User@p.Bla;->p.User:?;}
p.User:{'this\
 .m:p.User@p.User;\
->p.Bla:{'_\
 ? .bla[?]:p.User@!; .bla()->p.User:?;}:?.bla():?;}
""",List.of("""
User:{.m:User->
 Bla:{.bla:User->User;}.bla
}
"""));}

@Test void inLineAnonObject2(){ok("""
p.A_User:{'_\
 .bla:p.User@p.A_User;\
->p.User:?;}
p.User:{'this\
 .m:p.User@p.User;\
->p.A_User:{'_\
 ? .bla[?]:p.User@!; .bla()->p.User:?;}:?.bla():?;}
""",List.of("""
User:{.m:User->
 {.bla:User->User;}.bla
}
"""));}

@Test void magicWidenErrMispelled(){fail("""
In file: [###]/in_memory0.fear

002| A:base.Widen[A]{}
   |   ^^^^^^^^^^^

While inspecting a type name
Type "Widen" is not declared in package "base".
Did you mean "WidenTo" ?
Error 9 WellFormedness
""",List.of("""
A:base.Widen[A]{}
B:base.Widen[B]{}
C:A,B{}
"""));}

@Test void magicWidenErr(){fail("""
In file: [###]/in_memory0.fear

004| C:A,B{}
   | ^^

While inspecting the file
Type "p.C" implements base.WidenTo more than once.
At most one base.WidenTo[T] supertype is allowed, because it defines the preferred widened type.
Found the following base.WidenTo supertypes:
  - "base.WidenTo[p.A]"
  - "base.WidenTo[p.B]"
Error 9 WellFormedness
""",List.of("""
A:base.WidenTo[A]{}
B:base.WidenTo[B]{}
C:A,B{}
"""));}

@Test void bareSimple_undefined_noSuggestions_noOtherPkg(){fail("""
In file: [###]/in_memory0.fear

004|   .foo(x:Missing):Missing;
   |          ^^^^^^^^

While inspecting a type name
Type "Missing" is not declared in package "p" and is not made visible via "use".
In scope: "User".
Error 9 WellFormedness
""",List.of("""
User:{
 'this
  .foo(x:Missing):Missing;
}
"""));}

@Test void bareSimple_suggestFromScope(){fail("""
In file: [###]/in_memory0.fear

005|   .foo(x:Fod):Fod;
   |          ^^^^

While inspecting a type name
Type "Fod" is not declared in package "p" and is not made visible via "use".
Did you mean "Food" ?
In scope: "Food", "User".
Error 9 WellFormedness
""",List.of("""
Food:{}
User:{
 'this
  .foo(x:Fod):Fod;
}
"""));}

@Test void bareSimple_onlyInOtherPackage_crossPackageNote(){fail("""
In file: [###]/in_memory0.fear

004|   .foo(x:GG):G;
   |          ^^^

While inspecting a type name
Type "GG" is not declared in package "p" and is not made visible via "use".
In scope: "G", "User".
Error 9 WellFormedness
""","""
role app000;
use base.F as G;
""",List.of("""
User:{
 'this
  .foo(x:GG):G;
}
"""));}

@Test void bareSimple_onlyInOtherPackage_crossPackageImported(){fail("""
In file: [###]/in_memory0.fear

004|   .foo(x:F):F;
   |          ^^

While inspecting a type name
Type "F" is not declared in package "p" and is not made visible via "use".
In scope: "User".
Did you mean "base.F" ?
Add a "use" or write the fully qualified name.
Error 9 WellFormedness
""","""
role app000;
//use base.F as G;
""",List.of("""
User:{
 'this
  .foo(x:F):F;
}
"""));}

@Test void bareSimple_suggestAndCrossPackageNote(){fail("""
In file: [###]/in_memory0.fear

004|   .foo(xs:Blok):Blok;
   |           ^^^^^

While inspecting a type name
Type "Blok" is not declared in package "p" and is not made visible via "use".
In scope: "User".
Did you mean "base.Block" ?
Add a "use" or write the fully qualified name.
Error 9 WellFormedness
""",List.of("""
User:{
 'this
  .foo(xs:Blok):Blok;
}
"""));}

@Test void explicitPackage_pkgDoesNotExist_withSuggestion(){fail("""
In file: [###]/in_memory0.fear

003|   .foo(x:basee.F):basee.F;
   |          ^^^^^^^^

While inspecting a type name
Package "basee" does not exist.
Did you mean "base" ?
Visible packages: "base".
Error 9 WellFormedness
""","""
role app000;
use base.F as F;
""",List.of("""
User:{
  .foo(x:basee.F):basee.F;
}
"""));}

@Test void explicitPackage_typeNotInThatPackage_noArityIssue(){fail("""
In file: [###]/in_memory0.fear

003|   .foo(x:base.Foo):base.Foo;
   |          ^^^^^^^^^

While inspecting a type name
Type "Foo" is not declared in package "base".
Error 9 WellFormedness
""","""
role app000;
use base.F as F;
""",List.of("""
User:{
  .foo(x:base.Foo):base.Foo;
}
"""));}

@Test void explicitPackage_arityMismatch_listsAvailableArities(){fail("""
In file: [###]/in_memory0.fear

003|   .foo[X,Y](x:base.Block[X,Y]):base.Block[X,Y];
   |               ^^^^^^^^^^^

While inspecting a type name
Name "Block" is not declared with 2 generic parameter(s) in package "base".
Name "Block" is only declared with the following numbers of generic parameters: 0, 1.
Did you accidentally add or omit a generic type parameter?
Error 9 WellFormedness
""","""
role app000;
//use base.Block as Block;
""",List.of("""
User:{
  .foo[X,Y](x:base.Block[X,Y]):base.Block[X,Y];
}
"""));}

@Test void bareSimple_arityMismatch_prefersLocalAndShowsArities(){fail("""
In file: [###]/in_memory0.fear

003|   .foo[X,Y](x:Block[X,Y]):Block[X,Y];
   |               ^^^^^^

While inspecting a type name
Name "Block" is not declared with 2 generic parameter(s) in package "base".
Name "Block" is only declared with the following numbers of generic parameters: 0, 1.
Did you accidentally add or omit a generic type parameter?
Error 9 WellFormedness
""","""
role app000;
use base.Block as Block;
""",List.of("""
User:{
  .foo[X,Y](x:Block[X,Y]):Block[X,Y];
}
"""));}
@Test void bareSimple_caseTypos_suggestsCorrectCase(){fail("""
In file: [###]/in_memory0.fear

003| User:{ .foo(x:FOo):FOo; }
   |               ^^^^

While inspecting a type name
Type "FOo" is not declared in package "p" and is not made visible via "use".
Did you mean "Foo" ?
In scope: "Foo", "User".
Error 9 WellFormedness
""",List.of("""
Foo:{}
User:{ .foo(x:FOo):FOo; }
"""));}

@Test void bareSimple_inScopeListing_whenManyCandidates(){fail("""
In file: [###]/in_memory0.fear

005| User:{ .foo(x:Abc):Abc; }
   |               ^^^^

While inspecting a type name
Type "Abc" is not declared in package "p" and is not made visible via "use".
In scope: "Aaa", "Abb", "Acc", "User".
Error 9 WellFormedness
""",List.of("""
Aaa:{}
Abb:{}
Acc:{}
User:{ .foo(x:Abc):Abc; }
"""));}

@Test void genericTypeVarShadowsTName(){fail("""
In file: [###]/in_memory1.fear

002| Y[X:imm]:{}
   |   ^^

While inspecting a type name
Generic type parameter "X" is declared in package "p".
Name "X" is also used as a type name.
Error 9 WellFormedness
""",
  List.of("""
X:{}
""",
"""
Y[X:imm]:{}
"""));}

@Test void sameTypeInTwoFiles(){fail("""
In file: [###]/in_memory0.fear

002| X:{.foo:base.Void}
   | ^^

While inspecting a type name
Duplicate type declaration for "X".
Error 9 WellFormedness
""",
  List.of("""
X:{.foo:base.Void}
""",
"""
X:{.bar:base.Void}
"""));}

@Test void duplicateBoundType(){fail("""
In file: [###]/in_memory0.fear

002| X[A:imm,mut,imm]:{.bar:base.Void}
   |   ^^

While inspecting the file
Duplicate reference capability in the generic type parameter "A".
Reference capability "imm" is repeated.
Error 9 WellFormedness
""",
  List.of("""
X[A:imm,mut,imm]:{.bar:base.Void}
"""));}
@Test void duplicateBoundMeth(){fail("""
In file: [###]/in_memory0.fear

002| X:{.bar[A:imm,mut,imm]:base.Void}
   |         ^^

While inspecting the file
Duplicate reference capability in the generic type parameter "A".
Reference capability "imm" is repeated.
Error 9 WellFormedness
""",
  List.of("""
X:{.bar[A:imm,mut,imm]:base.Void}
"""));}

@Test void noSource(){fail("""
In file: [###]/in_memory0.fear

003| B:{base.Void}//forgot to implement A
   |    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Cannot infer signature of method ":?".
No supertype has a method with 0 parameters.
Error 9 WellFormedness
""",
  List.of("""
A:{.m:base.Void}
B:{base.Void}//forgot to implement A
"""));}
//Tested also here, but note that this is ensured by the parsing already
@Test void overOverloading(){fail("""
In file: [###]/in_memory0.fear

001| package p;
002| A:{imm .m:base.Void; imm .m:base.Void}
   | --~~~~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^

While inspecting type declaration body > type declaration > full file
Method ".m" redeclared.
A method with the same name, arity and reference capability is already present.
Error 9 WellFormedness
""",
List.of("""
A:{imm .m:base.Void; imm .m:base.Void}
"""));}

}
//TODO: in the guide somewhere show #|" foo{#U+`AB02`} for arbitrary Unicode
//TODO: well formedness for Sealed still missing