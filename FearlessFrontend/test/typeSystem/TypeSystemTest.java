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
@Test void tsMiniFail(){fail("""
002| A:{.foo123:A->this.ba}
   |    ---------------^^^

While inspecting the body of method ".foo123"
Call of method ".ba".
Such method is not declared on type "p.A".
Available methods:
  imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.ba}
"""));}

@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Test void tsOkIndirectFail1(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
   |                            ------------^^^^^^^

While inspecting the body of method ".bar"
Call of method ".foO123".
Such method is not declared on type "p.A".
Did you mean ".foo123" ?
Available methods:
  imm .bar:p.A;
  mut .bob(p.A):p.A;
  imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
"""));}

@Test void tsOkIndirectFail2(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
   |                            ------------^^^^^^

While inspecting the body of method ".bar"
Call of method ".foo23".
Such method is not declared on type "p.A".
Did you mean ".foo123" ?
Available methods:
  imm .bar:p.A;
  imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
"""));}

@Test void tsOkIndirectFail3(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
   |                            ------------^^^^^^^^

While inspecting the body of method ".bar"
Call of method ".foo1123".
Such method is not declared on type "p.A".
Did you mean ".foo123" ?
Available methods:
  imm .bar:p.A;
  imm .foo123:p.A;
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
"""));}//No, should say that did you mean... Should also list the methods of A

@Test void tsOkIndirectFail4(){fail("""
004|   .bar:A->this.foo123(this);
   |   ------------^^^^^^^^-----

While inspecting the body of method ".bar"
Method ".foo123" declared on type "p.A" but with different parameter count.
Call supplies 1 arguments, but available overloads take 0 or 3.
""",List.of("""
A:{
  .foo123:A->this.foo123; 
  .bar:A->this.foo123(this);
  .foo123(A,A,A):A->this.foo123;
  }
"""));}

@Test void tsOkIndirectFail4spaces(){fail("""
004|   .bar:A->this.foo123(this      );
   |   ------------^^^^^^^^-----------

While inspecting the body of method ".bar"
Method ".foo123" declared on type "p.A" but with different parameter count.
Call supplies 1 arguments, but available overloads take 0 or 3.
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

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: mut.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
      needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail6a(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                            -------------~~~~^^^^^^^

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
      needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Test void tsOkIndirectFail6b(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                            -------------~~~~^^^^^^^^~~~~

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
      needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}
@Test void tsOkIndirectFail6c(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
   |                            -----------------^^^^^^^^-----

While inspecting the body of method ".bar"
Method ".foo123" declared on type "p.A" exists, but not with the requested capability.
Call requires the existence of a "read" method.
Available capabilities for this method: imm.
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
"""));} 

@Test void tsOkIndirectFail7(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
   |                                ------------~~~~^^^^^^^

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: imm.
The generated promotions for this call require the receiver to be mut or iso or mutH.
Available method promotions:
  - `As declared`:
      needs receiver mut
  - `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`:
      needs receiver iso
  - `Allow mutH`:
      needs receiver mutH
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail8(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                            -------------~~~~^^^^^^^^~~~~

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`:
      needs receiver imm
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

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be mut or iso or mutH.
Available method promotions:
  - `As declared`:
      needs receiver mut
  - `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`:
      needs receiver iso
  - `Allow mutH`:
      needs receiver mutH
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

While inspecting the body of method ".bar"
Type mismatch.
The parameter "b" has type "p.B".
"p.B" is not a subtype of "p.A".
""",List.of("""
A:{ .bar(b:B):A->b; }
B:{ }
"""));}
@Test void uncallableMethodOk(){ok(List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{}; }
"""));}
@Disabled @Test void uncallableMethodFail(){fail("""

""",List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{ .bar->b}; }
"""));}

@Disabled @Test void methodReceiverNotRcc(){fail("""

""",List.of("""
A:{
  .foo123:A->this.foo123;
  .bar[X:imm,mut,read](x:X):A->x.foo123;
}
"""));}

@Disabled @Test void methodTArgsArityError(){fail("""

""",List.of("""
A:{
  .id[X:imm,mut,read](x:X):X->x;
  .bar:A->this.id[A,A](this);
}
"""));}

@Test void methodArgsDisagree(){fail("""
004|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^^~~~~

While inspecting the body of method ".caller"
Call of method ".f" can not be satisfied.
Each argument is compatible with some promotions, but no single promotion works for all arguments.
Compatible promotions by argument:
  - argument 0 has type readH p.A: `Allow readH`, Allow mutH (arg0)
  - argument 1 has type mutH p.A: Allow mutH (arg1)
Promotion failures:
  - fails at argument 0: `As declared`
    The parameter "x" has type "readH p.A".
    "readH p.A" is not a subtype of "read p.A".
  - fails at argument 0: `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow mutH`
    The parameter "x" has type "readH p.A".
    "readH p.A" is not a subtype of "p.A".
  - fails at argument 1: `Allow readH`, Allow mutH (arg0)
    The parameter "y" has type "mutH p.A".
    "mutH p.A" is not a subtype of "iso p.A".
  - fails at argument 0: Allow mutH (arg1)
    The parameter "x" has type "readH p.A".
    "readH p.A" is not a subtype of "p.A".
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

While inspecting the body of method ".foo" > the body of method ".f"
The parameter "aaaa" is not available in this scope.
Declared type: mut p.A.
The parameter "aaaa" (declared as "mut p.A") is hidden because
it is not visible from an imm scope.
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
}
"""));}

@Test void noVar2Fail(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
   |   ---------------------------------~~~~~~~~~~~~~~~~~~^~~~~~--

While inspecting the body of method ".foo" > the body of method ".f"
Call of method "#" can not be satisfied.
Argument 0 is incompatible with all available promotions.
Argument 0 has type "read p.A".
The parameter "aaaa" (declared as type "mut p.A") here has type "read p.A".
"read p.A" is not a subtype of "mut p.A".
Viewpoint adaptation set "aaaa" to "read p.A" from "mut p.A" (the declared type).

Promotion failures:
  - fails at argument 0: `As declared`
    Expected: "mut p.A".
  - fails at argument 0: `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`
    Expected: "iso p.A".
  - fails at argument 0: Allow mutH (arg0)
    Expected: "mutH p.A".
""",List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
}
"""));}
}