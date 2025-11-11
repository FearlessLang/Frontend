package inferenceGrammar;

import java.util.List;

import org.junit.jupiter.api.Test;

public class TestInferenceSteps {
  static void okI(String expected, List<String> input){ TestInference.ok(expected,"role app000;",input,true); }
  static void okI(String expected, String head, List<String> input){ TestInference.ok(expected,head,input,true); }
@Test void inferMini(){okI("""
p.A:{'this\
 .foo:p.A@p.A;->this:p.A.foo[imm]():p.A;}
""",List.of("""
A:{.foo:A->this.foo}
"""));}
@Test void inferMini2(){okI("""
p.A:{'this\
 .foo[X:imm](X):X@p.A;(x)->this:p.A.foo[imm,X](x:X):X;}
""",List.of("""
A:{.foo[X](x:X):X->this.foo(x)}
"""));}
@Test void inferMini3(){okI("""
p.F[A:imm, B:imm]:{'this #(A):B@p.F;}
p.User:{'this\
 .foo[X:imm](X,p.F[X,X]):X@p.User;\
(x, f)->f:p.F[X,X]#[imm](x:X):X;\
 .bar:p.User@p.User;\
->this:p.User.foo[imm,p.User](\
p.User:p.User,\
p.A_User:p.F[p.User,p.User]{'_ imm #(p.User):p.User@p.F;\
 (a_impl)->a_impl:p.User;}:p.F[p.User,p.User]):p.User;}
""",List.of("""
F[A,B]:{#(A):B}
User:{
  .foo[X](x:X,f:F[X,X]):X->f#x;
  .bar:User->this.foo(User,{::})
  }
"""));}

static String importMini="""
role app000;
use base.Nat as Nat;
use base.F as F;
use base.Bool  as Bool;
""";
static String stackStart="""
StackMatch[T,R]: {
  .empty: R;
  .elem(top:T, tail: Stack[T]): R;
  }
Stack[T]: {
  .match[R](m: StackMatch[T,R]): R -> m.empty;
  .fold[R](start:R, f: F[R,T,R]): R -> start;
  .map[R](f: F[T, R]): Stack[R] -> {};
  .filter(f: F[T,Bool]): Stack[T]-> {};
  +(e: T): Stack[T] -> { 
    .match(m) -> m.elem(e, this);
    .fold(start, f) -> f#(this.fold(start, f), e);
    .map(f) -> this.map(f) + ( f#(e) );
    .filter(f) -> f#(e).if{
      .then -> this.filter(f) + e;
      .else -> this.filter(f);
      };
    };
  }
""";
@Test void inferStackGuideExampleSumLit(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z0ExampleSum:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z0ExampleSum;\
(ns)->ns:p.Stack[base.Nat].fold[imm,base.Nat](\
base.0:base.Nat,p.A_Z0Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@base.F;\
 (n1, n2)->n1:base.Nat+[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
""",importMini,List.of(stackStart+"""
Z0ExampleSum: { #(ns: Stack[Nat]): Nat -> ns.fold(0, { n1,n2 -> n1 + n2 })  }
"""));}
@Test void inferStackGuideExampleTimesLit(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z1ExampleTimes:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z1ExampleTimes;\
(ns)->ns:p.Stack[base.Nat]\
.fold[imm,base.Nat](\
base.1:base.Nat,\
p.A_Z1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@base.F;\
 (n1, n2)->n1:base.Nat*[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
""",importMini,List.of(stackStart+"""
Z1ExampleTimes: { #(ns: Stack[Nat]): Nat -> ns.fold(1, { n1,n2 -> n1 * n2 })  }
"""));}

@Test void inferStackGuideExampleSumMatchLit(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z2Example:{'this\
 .sum(p.Stack[base.Nat]):base.Nat@p.Z2Example;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,base.Nat](\
p.A_Z2Ex:p.StackMatch[base.Nat,base.Nat]{'_\
 imm .empty:base.Nat@p.StackMatch;\
 .empty()->base.0:base.Nat;\
 imm .elem(base.Nat,p.Stack[base.Nat]):base.Nat@p.StackMatch;\
 .elem(top, tail)->top:base.Nat\
+[imm](this:p.Z2Example.sum[imm](tail:p.Stack[base.Nat]):base.Nat):base.Nat;\
}:p.StackMatch[base.Nat,base.Nat]):base.Nat;}
""",importMini,List.of(stackStart+"""
Z2Example: {
  .sum(ns: Stack[Nat]): Nat -> ns.match{
    .empty -> 0;
    .elem(top, tail) -> top + ( this.sum(tail) );
    }
  }
"""));}

@Test void inferStackGuideExampleAdd5Lit(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z3ExampleAdd5:{'this\
 .add5(p.Stack[base.Nat]):p.Stack[base.Nat]@p.Z3ExampleAdd5;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,p.Stack[base.Nat]](\
p.B_Z3Ex:p.StackMatch[base.Nat,p.Stack[base.Nat]]{'_\
 imm .empty:p.Stack[base.Nat]@p.StackMatch;\
 .empty()->p.Stack[base.Nat]:p.Stack[base.Nat];\
 imm .elem(base.Nat,p.Stack[base.Nat]):p.Stack[base.Nat]@p.StackMatch;\
 .elem(top, tail)->p.Z3ExampleAdd5:p.Z3ExampleAdd5\
.add5[imm](tail:p.Stack[base.Nat]):p.Stack[base.Nat]\
+[imm](top:base.Nat+[imm](base.5:base.Nat):base.Nat):p.Stack[base.Nat];\
}:p.StackMatch[base.Nat,p.Stack[base.Nat]]):p.Stack[base.Nat];}
""",importTo10,List.of(stackStart+"""
Z3ExampleAdd5:{
  .add5(ns: Stack[Nat]): Stack[Nat] -> ns.match{
    .empty -> {};
    .elem(top, tail) -> Z3ExampleAdd5.add5(tail) + (top + 5);
    }
  }
"""));}

@Test void inferStackGuideExampleFluentLit(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z4ExampleFluent:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z4ExampleFluent;\
(ns)->ns:p.Stack[base.Nat].map[imm,base.Nat](\
p.A_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@base.F;\
 (n)->n:base.Nat+[imm](base.10:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat]\
.map[imm,base.Nat](\
p.B_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@base.F;\
 (n)->n:base.Nat*[imm](base.3:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat].fold[imm,base.Nat](\
base.0:base.Nat,p.C_Z4Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@base.F;\
 (n1, n2)->n1:base.Nat+[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]\
):base.Nat;\
}
""",importMini,List.of(stackStart+"""
Z4ExampleFluent: { #(ns: Stack[Nat]): Nat -> ns
  .map { n -> n + 10 }
  .map { n -> n *  3 }
  .fold(0, { n1,n2 -> n1 + n2 })
  }
"""));}
//-----------Now with numbers as userDefNames
static String importTo10="""
role app000;
use base.Nat as Nat;
use base.F as F;
use base.Bool  as Bool;
use base.Zero  as Zero;
use base.One   as One;
use base.Two   as Two;
use base.Three as Three;
use base.Four  as Four;
use base.Five  as Five;
use base.Six   as Six;
use base.Seven as Seven;
use base.Eight as Eight;
use base.Nine  as Nine;
use base.Ten   as Ten;
"""; 
@Test void inferStackGuideExampleBase(){okI("""
p.Stack[T:imm]:{'this\
 .match[R:imm](p.StackMatch[T,R]):R@p.Stack;\
(m)->m:p.StackMatch[T,R].empty[imm]():R;\
 .fold[R:imm](R,base.F[R,T,R]):R@p.Stack;\
(start, f)->start:R;\
 .map[R:imm](base.F[T,R]):p.Stack[R]@p.Stack;\
(f)->p.Stack[R]:p.Stack[R];\
 .filter(base.F[T,base.Bool]):p.Stack[T]@p.Stack;\
(f)->p.Stack[T]:p.Stack[T];\
 +(T):p.Stack[T]@p.Stack;\
(e)->p.D_Stac:p.Stack[T]{'_\
 imm .match[R:imm](p.StackMatch[T,R]):R@p.Stack;\
 .match(m)->m:p.StackMatch[T,R].elem[imm](e:T,this:p.Stack[T]):R;\
 imm .fold[R:imm](R,base.F[R,T,R]):R@p.Stack;\
 .fold(start, f)->f:base.F[R,T,R]#[read](\
this:p.Stack[T].fold[imm,R](start:R,f:base.F[R,T,R]):R,e:T\
):R;\
 imm .map[R:imm](base.F[T,R]):p.Stack[R]@p.Stack;\
 .map(f)->this:p.Stack[T].map[imm,R](f:base.F[T,R]):p.Stack[R]\
+[imm](f:base.F[T,R]#[read](e:T):R):p.Stack[R];\
 imm .filter(base.F[T,base.Bool]):p.Stack[T]@p.Stack;\
 .filter(f)->f:base.F[T,base.Bool]#[read](e:T):base.Bool\
.if[imm,p.Stack[T]](mut p.C_Stac:base.ThenElse[p.Stack[T]]{'_\
 mut .then:p.Stack[T]@base.ThenElse;\
 .then()->this:p.Stack[T]\
.filter[imm](f:base.F[T,base.Bool]):p.Stack[T]\
+[imm](e:T):p.Stack[T];\
 mut .else:p.Stack[T]@base.ThenElse;\
 .else()->this:p.Stack[T]\
.filter[imm](f:base.F[T,base.Bool]):p.Stack[T];\
}:mut base.ThenElse[p.Stack[T]]):p.Stack[T];\
}:p.Stack[T];}
p.StackMatch[T:imm, R:imm]:{'this\
 .empty:R@p.StackMatch;\
 .elem(T,p.Stack[T]):R@p.StackMatch;}
""",importTo10,List.of(stackStart));}

@Test void inferStackGuideExampleSum(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z0ExampleSum:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z0ExampleSum;\
(ns)->ns:p.Stack[base.Nat].fold[imm,base.Nat](\
base.Zero:base.Nat,p.A_Z0Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@base.F;\
 (n1, n2)->n1:base.Nat+[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
""",importTo10,List.of(stackStart+"""
Z0ExampleSum: { #(ns: Stack[Nat]): Nat -> ns.fold(Zero, { n1,n2 -> n1 + n2 })  }
"""));}
@Test void inferStackGuideExampleTimes(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z1ExampleTimes:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z1ExampleTimes;\
(ns)->ns:p.Stack[base.Nat]\
.fold[imm,base.Nat](\
base.One:base.Nat,\
p.A_Z1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@base.F;\
 (n1, n2)->n1:base.Nat*[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
""",importTo10,List.of(stackStart+"""
Z1ExampleTimes: { #(ns: Stack[Nat]): Nat -> ns.fold(One, { n1,n2 -> n1 * n2 })  }
"""));}

@Test void inferStackGuideExampleSumMatch(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z2Example:{'this\
 .sum(p.Stack[base.Nat]):base.Nat@p.Z2Example;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,base.Nat](\
p.A_Z2Ex:p.StackMatch[base.Nat,base.Nat]{'_\
 imm .empty:base.Nat@p.StackMatch;\
 .empty()->base.Zero:base.Nat;\
 imm .elem(base.Nat,p.Stack[base.Nat]):base.Nat@p.StackMatch;\
 .elem(top, tail)->top:base.Nat\
+[imm](this:p.Z2Example.sum[imm](tail:p.Stack[base.Nat]):base.Nat):base.Nat;\
}:p.StackMatch[base.Nat,base.Nat]):base.Nat;}
""",importTo10,List.of(stackStart+"""
Z2Example: {
  .sum(ns: Stack[Nat]): Nat -> ns.match{
    .empty -> Zero;
    .elem(top, tail) -> top + ( this.sum(tail) );
    }
  }
"""));}

@Test void inferStackGuideExampleAdd5(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z3ExampleAdd5:{'this\
 .add5(p.Stack[base.Nat]):p.Stack[base.Nat]@p.Z3ExampleAdd5;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,p.Stack[base.Nat]](\
p.B_Z3Ex:p.StackMatch[base.Nat,p.Stack[base.Nat]]{'_\
 imm .empty:p.Stack[base.Nat]@p.StackMatch;\
 .empty()->p.Stack[base.Nat]:p.Stack[base.Nat];\
 imm .elem(base.Nat,p.Stack[base.Nat]):p.Stack[base.Nat]@p.StackMatch;\
 .elem(top, tail)->p.Z3ExampleAdd5:p.Z3ExampleAdd5\
.add5[imm](tail:p.Stack[base.Nat]):p.Stack[base.Nat]\
+[imm](top:base.Nat+[imm](base.Five:base.Nat):base.Nat):p.Stack[base.Nat];\
}:p.StackMatch[base.Nat,p.Stack[base.Nat]]):p.Stack[base.Nat];}
""",importTo10,List.of(stackStart+"""
Z3ExampleAdd5:{
  .add5(ns: Stack[Nat]): Stack[Nat] -> ns.match{
    .empty -> {};
    .elem(top, tail) -> Z3ExampleAdd5.add5(tail) + (top + Five);
    }
  }
"""));}

@Test void inferStackGuideExampleFluent(){okI("""
p.Stack[T:imm]:{[###]}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Z4ExampleFluent:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z4ExampleFluent;\
(ns)->ns:p.Stack[base.Nat].map[imm,base.Nat](\
p.A_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@base.F;\
 (n)->n:base.Nat+[imm](base.Ten:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat]\
.map[imm,base.Nat](\
p.B_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@base.F;\
 (n)->n:base.Nat*[imm](base.Three:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat].fold[imm,base.Nat](\
base.Zero:base.Nat,p.C_Z4Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@base.F;\
 (n1, n2)->n1:base.Nat+[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]\
):base.Nat;\
}
""",importTo10,List.of(stackStart+"""
Z4ExampleFluent: { #(ns: Stack[Nat]): Nat -> ns
  .map { n -> n + Ten }
  .map { n -> n *  Three }
  .fold(Zero, { n1,n2 -> n1 + n2 })
  }
"""));}



//TODO: make sure to test the following:
//method .m[X](x:Foo[X]):X implemented is specified as .m[Y](z)->...
//check that the inference 5a must get z:Foo[Y]

//TODO: if some error about rc disagreement can not be triggered any more, they should become asserts
//search for 'Reference capability disagreement'
}
