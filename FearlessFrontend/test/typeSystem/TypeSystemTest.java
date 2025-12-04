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
   |                ^^^^

While inspecting the file
Call of method ".ba" but method not declared on type "p.A".
""",List.of("""
A:{.foo123:A->this.ba}
"""));}//No, it should also list the methods of A

@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Test void tsOkIndirectFail1(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foO123;}
   |                                        ^^^^^^^^^

While inspecting the file
Call of method ".foO123" but method not declared on type "p.A".
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foO123;}
"""));}//No, should say that did you mean foo123 or similar.  
//Should also list the methods of A

@Test void tsOkIndirectFail2(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
   |                                        ^^^^^^^^

While inspecting the file
Call of method ".foo23" but method not declared on type "p.A".
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
"""));}//No, should say that did you mean... Should also list the methods of A

@Test void tsOkIndirectFail3(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
   |                                        ^^^^^^^^^^

While inspecting the file
Call of method ".foo1123" but method not declared on type "p.A".
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
"""));}//No, should say that did you mean... Should also list the methods of A

@Test void tsOkIndirectFail4(){fail("""
002| A:{.foo123:A->this.foo123; .bar:A->this.foo123(this);}
   |                                               ^^^^^^^^

While inspecting the file
Call of method ".foo123" but method not declared on type "p.A".
""",List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123(this);}
"""));}//Here should notice same name different parameters and discuss about it. Should also list the methods of A
@Test void tsOkIndirectFail5(){fail("""
002| A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
   |                                            ^^^^^^^^^

While inspecting the file//by adding a frame instead of a span we can get a better name here. Same comment applies everywhere.
Receiver capability mismatch for call .foo123.
Receiver capability: mut.//unclear if we talk about 'received the argument' or 'receiver the parameter value'.
//Anyway the error should mention both, and try to keep friendly accessible tone.
No promotion is callable from mut.//Unsure about always discussing promotions when no hope.
//On one side can be overwelming, on the other side keeps consistency (if we discuss for other cases)
//and keeps the concept of promotions in the mind of the programmers
Promotions require receiver in: imm.
//Is 'Base' the right name? overall all the promotion names can be discussed to make the more friendly/clear.
Promotions checked:
  - Base, Strong, Flexy, UseReadH, UseMutH+Rec: needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}//Here should notice same name+parameters and wrong RC. Should also list the methods of A
@Test void tsOkIndirectFail6a(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                                             ^^^^^^^^^

While inspecting the file
Receiver capability mismatch for call .foo123.
Receiver capability: read.
No promotion is callable from read.
Promotions require receiver in: imm.
Promotions checked:
  - Base, Strong, Flexy, UseReadH, UseMutH+Rec: needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Test void tsOkIndirectFail6b(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                    ^^^^^^^

While inspecting the file
Receiver capability mismatch for call .foo123.
Receiver capability: read.
No promotion is callable from read.
Promotions require receiver in: imm.
Promotions checked:
  - Base, Strong, Flexy, UseReadH, UseMutH+Rec: needs receiver imm
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}
@Test void tsOkIndirectFail6c(){fail("""
002| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
   |                                                    ^^^^^^^^

While inspecting the file
Call of method ".foo123" but method not declared on type "p.A".
""",List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
"""));}//but if we explicitly use [read] (or if inference were to infer [read] since is the only 'callable')
//we would get this different error that does not mention promotions
//technically correct, since .foo123[read] is a different method in overloading with .foo123[imm].
//But this may be very confusing for the programmer. Not sure what a good cohesive error strategy looks like here. 

@Test void tsOkIndirectFail7(){fail("""
002| A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
   |                                                ^^^^^^^^^

While inspecting the file
Call of method ".foo123" but method not declared on type "p.A".
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}//Here unclear what inference inferred (not mut otherwise would talk promotions?)
//but the error message must show the inferred signature or something.
@Test void tsOkIndirectFail8(){fail("""
002| A:{mut .foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                                                 ^^^^^^^^^

While inspecting the file
Call of method ".foo123" but method not declared on type "p.A".
""",List.of("""
A:{mut .foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//similar case to before





}