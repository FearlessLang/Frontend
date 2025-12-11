package typeSystem;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import inference.DbgBlock;
import inference.TestInference;
import message.FearlessException;
import pkgmerge.FrontendLogicMain;
import pkgmerge.OtherPackages;
import utils.Err;

public class TypeSystemTest {
  static void ok(List<String> input){ ok("role app000;",input); }
  static void ok(String head, List<String> input){
    var o= TestInference.oracle("p",head,input);
    OtherPackages other= DbgBlock.dbg();
    TestInference.printError(
      ()->new FrontendLogicMain().of(List.of(),o.allFiles(),o,other),
      o);
  }
  static void fail(String expected,List<String> input){
    fail("In file: [###]/in_memory0.fear\n\n"+expected+"Error 10 TypeError","role app000;",input);
  }
  static void fail(String expected,String head, List<String> input){
    var o= TestInference.oracle("p",head,input);
    OtherPackages other= DbgBlock.dbg();
    FearlessException fe= assertThrows(FearlessException.class,
      ()->new FrontendLogicMain().of(List.of(),o.allFiles(),o,other));
    var got= fe.render(o);
    Err.strCmp(expected,got);
  }
   
@Test void tsMiniOk(){ok(List.of("""
A:{.foo123:A->this.foo123}
"""));}
@Disabled @Test void tsMiniFail(){fail("""
002| A:{.foo123:A->this.ba}
   |    -----------~~~~^^^

While inspecting ".foo123" line 2
This call to method ".ba" does not type-check.
Such method is not declared on type "p.A".

Available methods:
  - imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.ba}
"""));}
//--------------
//--------------
//--------------
@Test void typeNotWellKinded_genericInstantiationViolatesBounds(){fail("""
004| User:{ imm .m(a:imm A[mut B]):base.Void; }
   | --------------------^^^^^^^^--------------

While inspecting Object literal "p.User"
The type "p.A[mut p.B]" is invalid.
Type argument 1 ("mut p.B") does not satisfy the bounds for type parameter "X" in "p.A".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User:{.m(A[mut B]):-.Void}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm A[mut B]):base.Void; }
"""));}

@Test void typeNotWellKinded_secondTypeArgViolatesBoundsInParamType(){fail("""
005| User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
   | --------------------^^^^^^^^^^^^^^--------------

While inspecting Object literal "p.User"
The type "p.A[p.B,mut p.C]" is invalid.
Type argument 2 ("mut p.C") does not satisfy the bounds for type parameter "Y" in "p.A".
Here "Y" can only use capabilities "iso" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User:{.m(A[B,mut C]):-.Void}
""", List.of("""
A[X:imm,Y:read,iso]:{}
B:{}
C:{}
User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
"""));}

@Test void typeNotWellKinded_nestedInnerGenericViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting Object literal "p.User"
The type "p.B[mut p.C]" is invalid.
Type argument 1 ("mut p.C") does not satisfy the bounds for type parameter "Y" in "p.B".
Here "Y" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User:{.m(A[B[mut C]]):-.Void}
""", List.of("""
A[X:imm]:{}
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_literalSupertypeViolatesBounds(){fail("""
004| User:A[mut B]{ .foo(b:B):B->b;}
   | -----^^^^^^^^------------------

While inspecting Object literal "p.User"
The type "p.A[mut p.B]" is invalid.
Type argument 1 ("mut p.B") does not satisfy the bounds for type parameter "X" in "p.A".
Here "X" can only use capabilities "imm" or "mutH" or "readH".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User:A[mut B]{.foo(b:B):B->b}
""", List.of("""
A[X:imm,readH,mutH]:{}
B:{}
User:A[mut B]{ .foo(b:B):B->b;}
"""));}

@Test void typeNotWellKinded_methodReturnTypeViolatesBounds(){fail("""
004| User:{ imm .m(a:imm B):imm A[mut B]; }
   | ---------------------------^^^^^^^^---

While inspecting Object literal "p.User"
The type "p.A[mut p.B]" is invalid.
Type argument 1 ("mut p.B") does not satisfy the bounds for type parameter "X" in "p.A".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User:{.m(B):A[mut B]}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm B):imm A[mut B]; }
"""));}

@Test void typeNotWellKinded_methodTypeArgViolatesBounds_simple(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting Method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("mut p.B") does not satisfy the bounds for type parameter "X" in "p.A.id(_)".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgSecondParamViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
   |        -------------------------------------------^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting Method call ".pair(_,_)" > ".m(_,_,_)" line 5
The call to ".pair(_,_)" is invalid.
Type argument 2 ("mut p.C") does not satisfy the bounds for type parameter "Y" in "p.A.pair(_,_)".
Here "Y" can only use capabilities "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.pair[imm,B,mut C](b,c)
""", List.of("""
A:{ imm .pair[X:imm,Y:read](x:X,y:Y):base.Void->{} }
B:{}
C:{}
User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
"""));}

@Test void typeNotWellKinded_methodTypeArgNestedViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
   |        ----------------------------------------------~~~~~~^^^^^^^^~~~~

While inspecting Method call ".use(_)" > ".m(_,_,_)" line 5
The type "p.B[mut p.C]" is invalid.
Type argument 1 ("mut p.C") does not satisfy the bounds for type parameter "Y" in "p.B".
Here "Y" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.use[imm,B[mut C]](b)
""", List.of("""
A:{ imm .use[X:imm](x:X):base.Void->{} }
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
"""));}

@Test void typeNotWellKinded_literalHeaderUsesTypeParamViolatingBounds(){fail("""
003| User[Y:read]:A[Y]{}
   | -------------^^^^--

While inspecting Object literal "p.User"
The type "p.A[Y]" is invalid.
Type argument 1 ("Y") does not satisfy the bounds for type parameter "X" in "p.A".
Here "X" can only use capabilities "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User[Y:read]:A[Y]{}
""", List.of("""
A[X:imm]:{}
User[Y:read]:A[Y]{}
"""));}

@Test void typeNotWellKinded_nestedTwiceInnerMostViolatesBounds(){fail("""
005| User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting Object literal "p.User"
The type "p.B[mut p.C]" is invalid.
Type argument 1 ("mut p.C") does not satisfy the bounds for type parameter "Y" in "p.B".
Here "Y" can only use capabilities "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut User:{.m(A[B[mut C]]):-.Void}
""", List.of("""
A[X:imm]:{}
B[Y:read]:{}
C:{}
User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeWithMultipleBounds(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting Method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("mut p.B") does not satisfy the bounds for type parameter "X" in "p.A.id(_)".
Here "X" can only use capabilities "imm" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}


@Test void typeNotWellKinded_methodTypeArgOnTypeInfer(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
   |        -----------------------------------^^^^^^^

While inspecting Method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("base.InferErr") does not satisfy the bounds for type parameter "X" in "p.A.id(_)".
Here "X" can only use capabilities "mut" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,-.InferErr](b)
""", List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
"""));}
//TODO: this used to print, hinting at some other issue in the compact printer 
//mut User:{.m(A,B):-Void->{a.id[mut B](b)}} ?? why mut here? Why meth sig printed as .m(A,B) with no par names
//but it prints correctly in typeNotWellKinded_literalSupertypeViolatesBounds,.. why??

@Test void typeNotWellKinded_methodTypeArgOnTypeInfer2(){fail("""
004| User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
   |        --------------------------------^^^^^^^

While inspecting Method call ".id(_)" > ".m(_,_)" line 4
The call to ".id(_)" is invalid.
Type argument 1 ("read p.B") does not satisfy the bounds for type parameter "X" in "p.A.id(_)".
Here "X" can only use capabilities "iso" or "mut".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,read B](b)
""", List.of("""
A:{ imm .id[X:mut,iso](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeInferFromRetType(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
"""));}
@Test void typeNotWellKinded_twistToPassInfer(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:mut B):read B->a.id(b); }
"""));}

//--------------
//--------------
//--------------
@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Disabled @Test void tsOkIndirectFail1(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
   |                            --------~~~~^^^^^^^

While inspecting ".bar" line 2
This call to method ".foO123" does not type-check.
Such method is not declared on type "p.A".
Did you mean ".foo123" ?

Available methods:
  - imm .bar:p.A;
  - mut .bob(p.A):p.A;
  - imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
"""));}

@Disabled @Test void tsOkIndirectFail2(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
   |                            --------~~~~^^^^^^

While inspecting ".bar" line 2
This call to method ".foo23" does not type-check.
Such method is not declared on type "p.A".
Did you mean ".foo123" ?

Available methods:
  - imm .bar:p.A;
  - imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
"""));}

@Disabled @Test void tsOkIndirectFail3(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
   |                            --------~~~~^^^^^^^^

While inspecting ".bar" line 2
This call to method ".foo1123" does not type-check.
Such method is not declared on type "p.A".
Did you mean ".foo123" ?

Available methods:
  - imm .bar:p.A;
  - imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
"""));}//No, should say that did you mean... Should also list the methods of A

@Disabled @Test void tsOkIndirectFail4(){fail("""
004|   .bar:A->this.foo123(this);
   |   --------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 4
This call to method ".foo123(_)" does not type-check.
There is a method ".foo123" on type "p.A", but with different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Relevant code with inferred types:
this.foo123(this)
""",List.of("""
A:{
  .foo123:A->this.foo123; 
  .bar:A->this.foo123(this);
  .foo123(A,A,A):A->this.foo123;
  }
"""));}

@Disabled @Test void tsOkIndirectFail4spaces(){fail("""
004|   .bar:A->this.foo123(this      );
   |   --------~~~~^^^^^^^^~~~~-------

While inspecting ".bar" line 4
This call to method ".foo123(_)" does not type-check.
There is a method ".foo123" on type "p.A", but with different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Relevant code with inferred types:
this.foo123(this)
""",List.of("""
A:{
  .foo123:A->this.foo123; 
  .bar:A->this.foo123(this      );
  .foo123(A,A,A):A->this.foo123;
  }
"""));}
@Disabled @Test void tsOkIndirectFail5(){fail("""
002| A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
   |                            ------------~~~~^^^^^^^

While inspecting ".bar" line 2
This call to method ".foo123" does not type-check.
The receiver (the expression before the method name) has capability "mut".
This call requires a receiver with capability "imm".

Promotion failures:
  - receiver fails for promotion `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
    Needs receiver "imm".

Relevant code with inferred types:
this.foo123
""",List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}
@Disabled @Test void tsOkIndirectFail6a(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                            -------------~~~~^^^^^^^

While inspecting ".bar" line 2
This call to method ".foo123" does not type-check.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Promotion failures:
  - receiver fails for promotion `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
    Needs receiver "imm".

Relevant code with inferred types:
this.foo123
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Disabled @Test void tsOkIndirectFail6b(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                            -------------~~~~^^^^^^^^~~~~

While inspecting ".bar" line 2
This call to method ".foo123" does not type-check.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Promotion failures:
  - receiver fails for promotion `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
    Needs receiver "imm".

Relevant code with inferred types:
this.foo123
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}
@Disabled @Test void tsOkIndirectFail6c(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
   |                            -------------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 2
This call to method ".foo123" does not type-check.
".foo123" exists on type "p.A", but not with the requested capability.
This call requires the existence of a "read" method.
Available capabilities for this method: "imm".

Relevant code with inferred types:
this.foo123[read]
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
"""));} 

@Disabled @Test void tsOkIndirectFail7(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
   |                                ------------~~~~^^^^^^^

While inspecting ".bar" line 2
This call to method ".foo123" does not type-check.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso" or "mutH".

Promotion failures:
  - receiver fails for promotion `As declared`:
    Needs receiver "mut".
  - receiver fails for promotion `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`:
    Needs receiver "iso".
  - receiver fails for promotion `Allow mutH`:
    Needs receiver "mutH".

Relevant code with inferred types:
this.foo123[mut]
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Disabled @Test void tsOkIndirectFail8(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                            -------------~~~~^^^^^^^^~~~~

While inspecting ".bar" line 2
This call to method ".foo123" does not type-check.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Promotion failures:
  - receiver fails for promotion `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
    Needs receiver "imm".

Relevant code with inferred types:
this.foo123
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}

@Test void tsOkIndirectInferredAsRead(){ok(List.of("""
A:{mut .foo123:A->this.foo123; read .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Disabled @Test void tsOkIndirectFail10(){fail("""
007|   read .bar:A->
008|     this.foo123[mut];
   |     ----^^^^^^^^----

While inspecting ".bar" line 7
This call to method ".foo123" does not type-check.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso" or "mutH".

Promotion failures:
  - receiver fails for promotion `As declared`:
    Needs receiver "mut".
  - receiver fails for promotion `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`:
    Needs receiver "iso".
  - receiver fails for promotion `Allow mutH`:
    Needs receiver "mutH".

Relevant code with inferred types:
this.foo123[mut]
""",List.of("""
A:{
  mut .foo123:A->
    this.foo123;
  imm .foo123:A->
    this.foo123;
  read .bar:A->
    this.foo123[mut];
  }
"""));}
@Disabled @Test void baseTypeError(){fail("""
002| A:{ .bar(b:B):A->b; }
   |     -------------^

While inspecting ".bar(_)" line 2
The parameter "b" here has type "p.B", that is not a subtype of "p.A".

Relevant code with inferred types:
b
""",List.of("""
A:{ .bar(b:B):A->b; }
B:{ }
"""));}
@Test void uncallableMethodOk(){ok(List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{}; }
"""));}
@Disabled @Test void uncallableMethodFail(){fail("""
003| A:{ mut .baz(b: B):B->{ .bar->b}; }
   |     --------------------^^^^^^^-

While inspecting ".baz(_)" line 3
Method "mut .bar" can never be called (dead code).
The object literal instance of "p.B" at line 3 is "imm".
Method "mut .bar" requires a "mut" receiver, which cannot be obtained from a "imm" object.
Hint: remove the implementation of method "mut .bar".

Relevant code with inferred types:
B{mut .bar:B->b}
""",List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{ .bar->b}; }
"""));}
@Disabled @Test void methodReceiverNotRcc(){fail("""
004|   .bar[X:imm,mut,read](x:X):A->x.foo123;
   |   -----------------------------~^^^^^^^

While inspecting ".bar(_)" line 4
This call to method ".foo123" does not type-check.
The receiver is the type parameter "X".
Type parameters cannot be receivers of method calls.

Relevant code with inferred types:
x.foo123
""",List.of("""
A:{
  .foo123:A->this.foo123;
  .bar[X:imm,mut,read](x:X):A->x.foo123;
}
"""));}

@Disabled @Test void methodTArgsArityError(){fail("""
004|   .bar:A->this.id[A,A](this);
   |   --------~~~~^^^^~~~~~~~~~~

While inspecting ".bar" line 4
This call to method ".id(_)" does not type-check.
Wrong number of type arguments for ".id(_)".
This method expects 1 type argument, but this call provides 2 type arguments.

Relevant code with inferred types:
this.id[imm,A,A](this)
""",List.of("""
A:{
  .id[X:imm,mut,read](x:X):X->x;
  .bar:A->this.id[A,A](this);
}
"""));}

@Disabled @Test void methodArgsDisagree(){fail("""
004|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 4
This call to method ".f(_,_)" does not type-check.
Each argument is compatible with at least one promotion, but no single promotion works for all arguments.
  - argument 1 is compatible with promotions: `Allow readH`, `Allow mutH (arg0)`.
  - argument 2 is compatible with promotions: `Allow mutH (arg1)`.

Promotion failures:
  - argument 1 fails for promotion `As declared`:
    The parameter "x" here has type "readH p.A", that is not a subtype of "read p.A".
  - argument 1 fails for promotion `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow mutH`:
    The parameter "x" here has type "readH p.A", that is not a subtype of "p.A".
  - argument 2 fails for promotion `Allow readH`, `Allow mutH (arg0)`:
    The parameter "y" here has type "mutH p.A", that is not a subtype of "iso p.A".
  - argument 1 fails for promotion `Allow mutH (arg1)`:
    The parameter "x" here has type "readH p.A", that is not a subtype of "p.A".

Relevant code with inferred types:
this.f(x,y)
""",List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Disabled @Test void methodArgsDisagree2(){fail("""
005|   .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
   |   --------------------------------~~~~^^^~~~~~~~~~~~~~~~

While inspecting ".caller(_,_)" line 5
This call to method ".f(_,_)" does not type-check.
Each argument is compatible with at least one promotion, but no single promotion works for all arguments.
- Argument 1 is compatible with promotions: Allow readH, Allow mutH (arg0).
- Argument 2 is compatible with promotions: Allow mutH (arg1).

Promotion failures:
- The parameter "x" here has type "readH p.A", that is not a subtype of "read p.A". (As declared)
- The parameter "x" here has type "readH p.A", that is not a subtype of "p.A". (Strengthen result)
- Return requirement not met.
  Expected: "iso p.A".
  Promotions: As declared, Strengthen result (allows readH/mutH), Allow readH, Allow mutH, Allow mutH (arg0). (Allow readH, Allow mutH (arg0))
- The parameter "x" here has type "readH p.A", that is not a subtype of "p.A". (Allow mutH (arg1))

Relevant code with inferred types:
this.f(x,ID#[imm,mutH A](y))
""",List.of("""
ID:{#[T:**](x:T):T->x}
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
}
"""));}

@Test void noVar1Ok(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->Skip#(aaaa);
}
"""));}
@Disabled @Test void noVar1Fail(){fail("""
005|   .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
   |   ---------------------------~~~~~~~~~~~~~~^^^^^--

While inspecting ".foo" line 5 > ".f(_)" line 5
The parameter "aaaa" is not available here.

The parameter "aaaa" has declared type "mut p.A".
"aaaa" cannot be captured in the method body of "imm .foo" (line 5 inside "p.BB").
The literal "p.BB" is "imm", thus "mut p.A" cannot be captured inside of it.
Hint: capture an immutable copy instead, or move this use outside the object literal.

Relevant code with inferred types:
aaaa
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
}
"""));}

@Disabled @Test void noVar1FailAnon(){fail("""
005|   .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
   |   ------------------------~~~~~~~~~~~~~~^^^^^--

While inspecting ".foo" line 5 > ".f(_)" line 5
The parameter "aaaa" is not available here.

The parameter "aaaa" has declared type "mut p.A".
"aaaa" cannot be captured in the method body of "imm .foo" (line 5 inside instance of "p.B").
The literal instance of "p.B" is "imm", thus "mut p.A" cannot be captured inside of it.
Hint: capture an immutable copy instead, or move this use outside the object literal.

Relevant code with inferred types:
aaaa
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
}
"""));}


@Disabled @Test void noVar2Fail(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
   |                                    -------------~~~~^^~~~~~

While inspecting ".foo" line 5 > ".f(_)" line 5
This call to method "#(_)" does not type-check.
Argument 1 is incompatible with all available promotions.

The parameter "aaaa" (declared as type "mut p.A") here has type "read p.A".
Note: the declared type "mut p.A" would work for: `Allow mutH (arg0)`, `As declared`.
Viewpoint adaptation set "aaaa" to "read p.A" from "mut p.A" (the declared type).

Promotion failures:
  - argument 1 fails for promotion `As declared`:
    "read p.A" is not a subtype of "mut p.A".
  - argument 1 fails for promotion `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
    "read p.A" is not a subtype of "iso p.A".
  - argument 1 fails for promotion `Allow mutH (arg0)`:
    "read p.A" is not a subtype of "mutH p.A".

Relevant code with inferred types:
Skip#[imm,mut A](aaaa)
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
}
"""));}

@Test void correctDeepCall(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,read A](Id#[imm,read A](aaaa));}}
"""));}//TODO: this works with either one of the method targs explicitly listed
@Disabled @Test void badDeepCall(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
   |                                    -------------------~~^^~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "#(_)" does not type-check.
Argument 1 is incompatible with all available promotions.

The parameter "aaaa" (declared as type "mut p.A") here has type "read p.A".
Note: the declared type "mut p.A" would work for: `Allow mutH (arg0)`, `As declared`.
Viewpoint adaptation set "aaaa" to "read p.A" from "mut p.A" (the declared type).

Promotion failures:
  - argument 1 fails for promotion `As declared`:
    "read p.A" is not a subtype of "mut p.A".
  - argument 1 fails for promotion `Strengthen result`, `Strengthen result (allows readH/mutH)`:
    "read p.A" is not a subtype of "iso p.A".
  - argument 1 fails for promotion `Allow readH`, `Allow mutH`:
    "read p.A" is not a subtype of "iso p.A".
  - argument 1 fails for promotion `Allow mutH (arg0)`:
    "read p.A" is not a subtype of "mutH p.A".

Relevant code with inferred types:
Id#[imm,mut A](aaaa)
""",List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
"""));}//This fails because inference infers [mut A] instead of [read A]
//TODO: make the error message show the inference somehow

@Disabled @Test void hopelessArg_calls_pArgHasType(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "#(_)" does not type-check.
Argument 1 has type "read p.A".
That is not a subtype of any of "mut p.A" or "mutH p.A" or "iso p.A".

Type required by each promotion:
- "mut p.A" (As declared)
- "mutH p.A" (Allow mutH (arg0))
- "iso p.A" (Strengthen result)

Relevant code with inferred types:
Need#(AsRead#(aaaa))
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));} 
//TODO: make the test above less tabular,
//reduce the text in While inspecting the body of method ".foo" > the body of method ".f(_)"
//may be just While inspecting body of ".foo" > body of ".f(_)"
//find ways so that the error reports the inferred generic instantiation.
//maybe even print symbolically the 'code around'? 
}