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
   |                            ----------------^^^^^^^

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: mut.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`: needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail6a(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                            -----------------^^^^^^^

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`: needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Test void tsOkIndirectFail6b(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                            -----------------^^^^^^^^----

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`: needs receiver imm
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
   |                                ----------------^^^^^^^

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: imm.
The generated promotions for this call require the receiver to be mut or iso or mutH.
Available method promotions:
  - `As declared`: needs receiver mut
  - `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`: needs receiver iso
  - `Allow mutH`: needs receiver mutH
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail8(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                            -----------------^^^^^^^^----

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be imm.
Available method promotions:
  - `As declared`, `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`, `Allow mutH`: needs receiver imm
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}

@Test void tsOkIndirectInferredAsRead(){ok(List.of("""
A:{mut .foo123:A->this.foo123; read .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail10(){fail("""
007|   read .bar:A->
008|     this.foo123[mut];
   |         ^^^^^^^^

While inspecting the body of method ".bar"
Receiver capability mismatch for call ".foo123".
The receiver (the object on which the method is called) has capability: read.
The generated promotions for this call require the receiver to be mut or iso or mutH.
Available method promotions:
  - `As declared`: needs receiver mut
  - `Strengthen result`, `Strengthen result (allows readH/mutH)`, `Allow readH`: needs receiver iso
  - `Allow mutH`: needs receiver mutH
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
}