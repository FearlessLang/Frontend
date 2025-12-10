package typeSystem;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;

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
@Test void tsMiniFail(){fail("""
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

@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Test void tsOkIndirectFail1(){fail("""
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

@Test void tsOkIndirectFail2(){fail("""
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

@Test void tsOkIndirectFail3(){fail("""
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

@Test void tsOkIndirectFail4(){fail("""
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

@Test void tsOkIndirectFail4spaces(){fail("""
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
@Test void tsOkIndirectFail5(){fail("""
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
@Test void tsOkIndirectFail6a(){fail("""
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
@Test void tsOkIndirectFail6b(){fail("""
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
@Test void tsOkIndirectFail6c(){fail("""
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

@Test void tsOkIndirectFail7(){fail("""
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
@Test void tsOkIndirectFail8(){fail("""
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
@Test void tsOkIndirectFail10(){fail("""
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
@Test void baseTypeError(){fail("""
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
@Test void uncallableMethodFail(){fail("""
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
@Test void methodReceiverNotRcc(){fail("""
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

@Test void methodTArgsArityError(){fail("""
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

@Test void methodArgsDisagree(){fail("""
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
@Test void noVar1Ok(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->Skip#(aaaa);
}
"""));}
@Test void noVar1Fail(){fail("""
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

@Test void noVar1FailAnon(){fail("""
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


@Test void noVar2Fail(){fail("""
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
@Test void badDeepCall(){fail("""
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

@Test void hopelessArg_calls_pArgHasType(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "#(_)" does not type-check.
Argument 1 is incompatible with all available promotions.
Argument 1 has type "read p.A".

Promotion failures:
  - argument 1 fails for promotion `As declared`:
    Expected: "mut p.A".
    Return requirement not met.
    Expected: "mut p.A".
    Promotions: `Allow readH`, `Allow mutH (arg0)`, `As declared`.
  - argument 1 fails for promotion `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
    Expected: "iso p.A".
    Return requirement not met.
    Expected: "iso p.A".
    Promotions: `Allow readH`, `Allow mutH (arg0)`, `As declared`.
  - argument 1 fails for promotion `Allow mutH (arg0)`:
    Expected: "mutH p.A".
    Return requirement not met.
    Expected: "mutH p.A".
    Promotions: `Allow readH`, `Allow mutH (arg0)`, `As declared`.

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