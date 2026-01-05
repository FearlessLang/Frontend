package inference;

import java.util.List;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

public class TestInferenceSteps extends testUtils.FearlessTestBase{
  static void okI(String expected,List<String> input){ inferenceOk(expected, defaultHead, input, true); }
  static void okI(String expected,String head,List<String> input){ inferenceOk(expected, head, input, true); }
  static void failI(String expected, List<String> input){ inferenceFail(expected, defaultHead, input, true); }
  static void failI(String expected, String head, List<String> input){ inferenceFail(expected, head, input, true); }

@Test void inferMini(){okI("""
p.A:{'this .foo:p.A@p.A;->this:?.foo():?;}
~-----------
~mut p.A:{'this .foo:p.A->this.foo[imm]}

""",List.of("""
A:{.foo:A->this.foo}
"""));}
@Test void inferMini2(){okI("""
p.A:{'this .foo[X:imm](X):X@p.A;(x)->this:?.foo(x:?):?;}
~-----------
~mut p.A:{'this .foo[X:imm](x:X):X->this.foo[imm,imm X](x)}
""",List.of("""
A:{.foo[X](x:X):X->this.foo(x)}
"""));}
@Test void inferMini3(){okI("""
p.F[A:imm, B:imm]:{'this #(A):B@p.F;}
p.User:{'this .foo[X:imm](X,p.F[X,X]):X@p.User;(x, f)->f:?#(x:?):?; .bar:p.User@p.User;->this:?.foo(p.User:?,p._AUser:$?{'_ ? [?](?):?@!;(_aimpl)->_aimpl:?;}:?):?;}
p._AUser:p.F[p.User,p.User]{'_ #(p.User):p.User@p._AUser;(_aimpl)->_aimpl:p.User;}
~-----------
~mut p.F[A:imm,B:imm]:{'this #(_:A):B}
~mut p.User:{'this .foo[X:imm](x:X, f:p.F[X,X]):X->f#[imm](x); .bar:p.User->this.foo[imm,p.User](p.User, imm p._AUser:p.F[p.User,p.User]{'_ #(_aimpl:p.User):p.User->_aimpl})}
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
use base.Void as Void;
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
[###]~-----------
~mut p.StackMatch[###]
~mut p.Stack[###]
~mut p.Z0ExampleSum:{'this #(ns:p.Stack[base.Nat]):base.Nat\
->ns.fold[imm,base.Nat](base.0,\
 imm p._AZ0Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(n1:base.Nat, n2:base.Nat):base.Nat->n1+[imm](n2)})}
""",importMini,List.of(stackStart+"""
Z0ExampleSum: { #(ns: Stack[Nat]): Nat -> ns.fold(0, { n1,n2 -> n1 + n2 })  }
"""));}
@Test void inferStackGuideExampleTimesLit(){okI("""
p.StackMatch[###]
p.Stack[###]
p.Z1ExampleTimes:{'this #(p.Stack[base.Nat]):base.Nat@p.Z1ExampleTimes;(ns)->ns:?.fold(base.1:?,p._AZ1Ex:$?{'_ ? [?](?,?):?@!;(n1, n2)->n1:?*(n2:?):?;}:?):?;}
p._AZ1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_ read #(base.Nat,base.Nat):base.Nat@p._AZ1Ex;(n1, n2)->n1:?*(n2:base.Nat):base.Nat;}
p._CStac[T:imm]:base.ThenElse[p.Stack[imm T]]{'_ mut .then:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T]+[imm](e:imm T):p.Stack[imm T]; mut .else:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T];}
p._DStac[T:imm]:p.Stack[imm T]{'_ .match[_GR:imm](p.StackMatch[imm T,_GR]):_GR@p._DStac;(m)->m:p.StackMatch[imm T,imm _GR].elem[imm](e:imm T,this:p.Stack[imm T]):imm _GR; .fold[_HR:imm](_HR,base.F[_HR,imm T,_HR]):_HR@p._DStac;(start, f)->f:base.F[imm _HR,imm T,imm _HR]#[read](this:AnyRC p.Stack[imm T].fold[imm,imm _HR](start:imm _HR,f:base.F[imm _HR,imm T,imm _HR]):imm _HR,e:imm T):imm _HR; .map[_JR:imm](base.F[imm T,_JR]):p.Stack[_JR]@p._DStac;(f)->this:AnyRC p.Stack[imm T].map[imm,imm _JR](f:base.F[imm T,imm _JR]):p.Stack[imm _JR]+[imm](f:AnyRC base.F[imm T,imm _JR]#[read](e:imm T):imm _JR):p.Stack[imm _JR]; .filter(base.F[imm T,base.Bool]):p.Stack[imm T]@p._DStac;(f)->f:base.F[imm T,base.Bool]#[read](e:imm T):base.Bool.if[imm,p.Stack[imm T]](mut p._CStac[T:imm]:base.ThenElse[p.Stack[imm T]]{'_ mut .then:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T]+[imm](e:imm T):p.Stack[imm T]; mut .else:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T];}:mut base.ThenElse[p.Stack[imm T]]):p.Stack[imm T]; +(imm T):p.Stack[imm T]@p.Stack;}
~-----------
~mut p.StackMatch[###]
~mut p.Stack[###]
~mut p.Z1ExampleTimes:{'this #(ns:p.Stack[base.Nat]):base.Nat\
->ns.fold[imm,base.Nat](base.1, imm p._AZ1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(n1:base.Nat, n2:base.Nat):base.Nat->n1*[imm](n2)})}
""",importMini,List.of(stackStart+"""
Z1ExampleTimes: { #(ns: Stack[Nat]): Nat -> ns.fold(1, { n1,n2 -> n1 * n2 })  }
"""));}

@Test void inferStackGuideExampleSumMatchLit(){okI("""
[###]~-----------
~mut p.StackMatch[###]
~mut p.Stack[###]
~mut p.Z2Example:{'this .sum(ns:p.Stack[base.Nat]):base.Nat\
->ns.match[imm,base.Nat](imm p._AZ2Ex:p.StackMatch[base.Nat,base.Nat]{'_\
 .empty:base.Nat->base.0;\
 .elem(top:base.Nat, tail:p.Stack[base.Nat]):base.Nat\
->top+[imm](this.sum[imm](tail))})}
""",importMini,List.of(stackStart+"""
Z2Example: {
  .sum(ns: Stack[Nat]): Nat -> ns.match{
    .empty -> 0;
    .elem(top, tail) -> top + ( this.sum(tail) );
    }
  }
"""));}

@Test void inferStackGuideExampleAdd5Lit(){okI("""
[###]~-----------
~mut p.StackMatch[T:imm,R:imm]:{[###]}
~mut p.Stack[T:imm]:{[###]}
~mut p.Z3ExampleAdd5:{'this\
 .add5(ns:p.Stack[base.Nat]):p.Stack[base.Nat]->\
ns.match[imm,p.Stack[base.Nat]](\
imm p._BZ3Ex:p.StackMatch[base.Nat,p.Stack[base.Nat]]{'_\
 .empty:p.Stack[base.Nat]->p.Stack[base.Nat];\
 .elem(top:base.Nat, tail:p.Stack[base.Nat]):p.Stack[base.Nat]->\
p.Z3ExampleAdd5.add5[imm](tail)+[imm](top+[imm](base.5))})}
""",importTo10,List.of(stackStart+"""
Z3ExampleAdd5:{
  .add5(ns: Stack[Nat]): Stack[Nat] -> ns.match{
    .empty -> {};
    .elem(top, tail) -> Z3ExampleAdd5.add5(tail) + (top + 5);
    }
  }
"""));}

@Test void inferStackGuideExampleFluentLit(){okI("""
[###]~-----------
~mut p.StackMatch[T:imm,R:imm]:{[###]}
~mut p.Stack[T:imm]:{[###]}
~mut p.Z4ExampleFluent:{'this\
 #(ns:p.Stack[base.Nat]):base.Nat->ns\
.map[imm,base.Nat](imm p._AZ4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(n:base.Nat):base.Nat->n+[imm](base.10)})\
.map[imm,base.Nat](imm p._BZ4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(n:base.Nat):base.Nat->n*[imm](base.3)})\
.fold[imm,base.Nat](base.0,\
 imm p._CZ4Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(n1:base.Nat, n2:base.Nat):base.Nat->n1+[imm](n2)})}
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
p.StackMatch[T:imm, R:imm]:{'this .empty:R@p.StackMatch; .elem(T,p.Stack[T]):R@p.StackMatch;}
p.Stack[T:imm]:{'this .match[R:imm](p.StackMatch[T,R]):R@p.Stack;(m)->m:?.empty():?; .fold[R:imm](R,base.F[R,T,R]):R@p.Stack;(start, f)->start:?; .map[R:imm](base.F[T,R]):p.Stack[R]@p.Stack;(f)->p._AStac:$?:?; .filter(base.F[T,base.Bool]):p.Stack[T]@p.Stack;(f)->p._BStac:$?:?; +(T):p.Stack[T]@p.Stack;(e)->p._DStac:$?{'_ ? .match[?](?):?@!;(m)->m:?.elem(e:?,this:?):?; ? .fold[?](?,?):?@!;(start, f)->f:?#(this:?.fold(start:?,f:?):?,e:?):?; ? .map[?](?):?@!;(f)->this:?.map(f:?):?+(f:?#(e:?):?):?; ? .filter[?](?):?@!;(f)->f:?#(e:?):?.if(p._CStac:$?{'_ ? .then[?]:?@!;->this:?.filter(f:?):?+(e:?):?; ? .else[?]:?@!;->this:?.filter(f:?):?;}:?):?;}:?;}
p._CStac[T:imm]:base.ThenElse[p.Stack[imm T]]{'_ mut .then:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T]+[imm](e:imm T):p.Stack[imm T]; mut .else:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T];}
p._DStac[T:imm]:p.Stack[imm T]{'_ .match[_GR:imm](p.StackMatch[imm T,_GR]):_GR@p._DStac;(m)->m:p.StackMatch[imm T,imm _GR].elem[imm](e:imm T,this:p.Stack[imm T]):imm _GR; .fold[_HR:imm](_HR,base.F[_HR,imm T,_HR]):_HR@p._DStac;(start, f)->f:base.F[imm _HR,imm T,imm _HR]#[read](this:AnyRC p.Stack[imm T].fold[imm,imm _HR](start:imm _HR,f:base.F[imm _HR,imm T,imm _HR]):imm _HR,e:imm T):imm _HR; .map[_JR:imm](base.F[imm T,_JR]):p.Stack[_JR]@p._DStac;(f)->this:AnyRC p.Stack[imm T].map[imm,imm _JR](f:base.F[imm T,imm _JR]):p.Stack[imm _JR]+[imm](f:AnyRC base.F[imm T,imm _JR]#[read](e:imm T):imm _JR):p.Stack[imm _JR]; .filter(base.F[imm T,base.Bool]):p.Stack[imm T]@p._DStac;(f)->f:base.F[imm T,base.Bool]#[read](e:imm T):base.Bool.if[imm,p.Stack[imm T]](mut p._CStac[T:imm]:base.ThenElse[p.Stack[imm T]]{'_ mut .then:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T]+[imm](e:imm T):p.Stack[imm T]; mut .else:p.Stack[imm T]@p._CStac;->this:AnyRC p.Stack[imm T].filter[imm](f:base.F[imm T,base.Bool]):p.Stack[imm T];}:mut base.ThenElse[p.Stack[imm T]]):p.Stack[imm T]; +(imm T):p.Stack[imm T]@p.Stack;}
~-----------
~mut p.StackMatch[T:imm,R:imm]:{'this .empty:R; .elem(_:T, _:p.Stack[T]):R}
~mut p.Stack[T:imm]:{'this .match[R:imm](m:p.StackMatch[T,R]):R->m.empty[imm]; .fold[R:imm](start:R, f:base.F[R,T,R]):R->start; .map[R:imm](f:base.F[T,R]):p.Stack[R]->p.Stack[imm R]; .filter(f:base.F[T,base.Bool]):p.Stack[T]->p.Stack[imm T]; +(e:T):p.Stack[T]->imm p._DStac[T:imm]:p.Stack[imm T]{'_ .match[_GR:imm](m:p.StackMatch[imm T,_GR]):_GR->m.elem[imm](e, this); .fold[_HR:imm](start:_HR, f:base.F[_HR,imm T,_HR]):_HR->f#[read](this.fold[imm,imm _HR](start, f), e); .map[_JR:imm](f:base.F[imm T,_JR]):p.Stack[_JR]->this.map[imm,imm _JR](f)+[imm](f#[read](e)); .filter(f:base.F[imm T,base.Bool]):p.Stack[imm T]->f#[read](e).if[imm,p.Stack[imm T]](mut p._CStac[T:imm]:base.ThenElse[p.Stack[imm T]]{'_ mut .then:p.Stack[imm T]->this.filter[imm](f)+[imm](e); mut .else:p.Stack[imm T]->this.filter[imm](f)}); +(_:imm T):p.Stack[imm T]}}
""",importTo10,List.of(stackStart));}

@Test void inferStackGuideExampleSum(){okI("""
[###]~-----------
~mut p.StackMatch[T:imm,R:imm]:{[###]}
~mut p.Stack[T:imm]:{[###]}
~mut p.Z0ExampleSum:{'this\
 #(ns:p.Stack[base.Nat]):base.Nat->\
ns.fold[imm,base.Nat](base.Zero,\
 imm p._AZ0Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(n1:base.Nat, n2:base.Nat):base.Nat->n1+[imm](n2)})}
""",importTo10,List.of(stackStart+"""
Z0ExampleSum: { #(ns: Stack[Nat]): Nat -> ns.fold(Zero, { n1,n2 -> n1 + n2 })  }
"""));}
@Test void inferStackGuideExampleTimes(){okI("""
[###]~-----------
~mut p.StackMatch[T:imm,R:imm]:{[###]}
~mut p.Stack[T:imm]:{[###]}
~mut p.Z1ExampleTimes:{'this\
 #(ns:p.Stack[base.Nat]):base.Nat->\
ns.fold[imm,base.Nat](base.One,\
 imm p._AZ1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(n1:base.Nat, n2:base.Nat):base.Nat->n1*[imm](n2)})}
""",importTo10,List.of(stackStart+"""
Z1ExampleTimes: { #(ns: Stack[Nat]): Nat -> ns.fold(One, { n1,n2 -> n1 * n2 })  }
"""));}

@Test void inferStackGuideExampleSumMatch(){okI("""
[###]~-----------
~mut p.StackMatch[###]
~mut p.Stack[###]
~mut p.Z2Example:{'this .sum(ns:p.Stack[base.Nat]):base.Nat\
->ns.match[imm,base.Nat](\
imm p._AZ2Ex:p.StackMatch[base.Nat,base.Nat]{'_\
 .empty:base.Nat->base.Zero;\
 .elem(top:base.Nat, tail:p.Stack[base.Nat]):base.Nat\
->top+[imm](this.sum[imm](tail))})}
""",importTo10,List.of(stackStart+"""
Z2Example: {
  .sum(ns: Stack[Nat]): Nat -> ns.match{
    .empty -> Zero;
    .elem(top, tail) -> top + ( this.sum(tail) );
    }
  }
"""));}

@Test void inferStackGuideExampleAdd5(){okI("""
[###]~-----------
~mut p.StackMatch[T:imm,R:imm]:{[###]}
~mut p.Stack[T:imm]:{[###]}
~mut p.Z3ExampleAdd5:{'this .add5(ns:p.Stack[base.Nat]):p.Stack[base.Nat]\
->ns.match[imm,p.Stack[base.Nat]](\
imm p._BZ3Ex:p.StackMatch[base.Nat,p.Stack[base.Nat]]{'_\
 .empty:p.Stack[base.Nat]->p.Stack[base.Nat];\
 .elem(top:base.Nat, tail:p.Stack[base.Nat]):p.Stack[base.Nat]\
->p.Z3ExampleAdd5.add5[imm](tail)+[imm](top+[imm](base.Five))})}
""",importTo10,List.of(stackStart+"""
Z3ExampleAdd5:{
  .add5(ns: Stack[Nat]): Stack[Nat] -> ns.match{
    .empty -> {};
    .elem(top, tail) -> Z3ExampleAdd5.add5(tail) + (top + Five);
    }
  }
"""));}

@Test void inferStackGuideExampleFluent(){okI("""
[###]~-----------
~mut p.StackMatch[###]
~mut p.Stack[###]
~mut p.Z4ExampleFluent:{'this #(ns:p.Stack[base.Nat]):base.Nat\
->ns.map[imm,base.Nat](imm p._AZ4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(n:base.Nat):base.Nat->n+[imm](base.Ten)})\
.map[imm,base.Nat](imm p._BZ4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(n:base.Nat):base.Nat->n*[imm](base.Three)})\
.fold[imm,base.Nat](base.Zero, imm p._CZ4Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(n1:base.Nat, n2:base.Nat):base.Nat->n1+[imm](n2)})}
""",importTo10,List.of(stackStart+"""
Z4ExampleFluent: { #(ns: Stack[Nat]): Nat -> ns
  .map { n -> n + Ten }
  .map { n -> n *  Three }
  .fold(Zero, { n1,n2 -> n1 + n2 })
  }
"""));}

@Test void boundChangesName(){okI("""
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1:p.A{'this .m[Y:imm](p.Foo[Y]):Y@p.B1;(z)->z:?.get():?;}
p.B2:p.A{'this .m[Y:imm](p.Foo[Y]):Y@p.B2;(z)->z:?.beer[Y]():?;}
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
~-----------
~mut p.A:{'this .m[X:imm](_:p.Foo[X]):X}
~mut p.B1:p.A{'this .m[Y:imm](z:p.Foo[Y]):Y->z.get[imm]}
~mut p.B2:p.A{'this .m[Y:imm](z:p.Foo[Y]):Y->z.beer[imm,Y]}
~mut p.Foo[K:imm]:{'this .get:K; .beer[G:imm]:G}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1:A{.m[Y](z)->z.get}
B2:A{.m[Y](z)->z.beer[Y]}
"""));}

@Test void inferAlpha_Rename_SingleSuper_UserNamesWin(){ okI("""
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.B:p.A{'this .id[T:imm](p.Box[T]):T@p.B;(b)->b:?.get():?;}
p.Box[K:imm]:{'this .get:K@p.Box;}
~-----------
~mut p.A:{'this .id[X:imm](_:p.Box[X]):X}
~mut p.B:p.A{'this .id[T:imm](b:p.Box[T]):T->b.get[imm]}
~mut p.Box[K:imm]:{'this .get:K}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X](x:Box[X]):X}
B:A{.id[T](b:Box[T])->b.get}
"""));
}

@Test void inferAlpha_Rename_SwapOrderInOverride(){ okI("""
p.A:{'this .pick[X:imm,Y:imm](p.Pair[X,Y]):Y@p.A;}
p.B:p.A{'this .pick[U:imm,V:imm](p.Pair[V,U]):V@p.B;(p)->p:?.fst():?;}
p.Pair[AA:imm, BB:imm]:{'this .fst:AA@p.Pair; .snd:BB@p.Pair;}
~-----------
~mut p.A:{'this .pick[X:imm,Y:imm](_:p.Pair[X,Y]):Y}
~mut p.B:p.A{'this .pick[U:imm,V:imm](p:p.Pair[V,U]):V->p.fst[imm]}
~mut p.Pair[AA:imm,BB:imm]:{'this .fst:AA; .snd:BB}
""", List.of("""
Pair[AA,BB]:{.fst:AA;.snd:BB;}
A:{.pick[X,Y](p:Pair[X,Y]):Y}
B:A{.pick[U,V](p:Pair[V,U])->p.fst}
"""));
}

@Test void inferAlpha_MultiSuper_SameBounds_SameMeaning_DifferentNames(){ okI("""
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.Box[K:imm]:{'this .get:K@p.Box;}
p.C:{'this .id[Y:imm](p.Box[Y]):Y@p.C;}
p.D:p.A, p.C{'this .id[X:imm](p.Box[X]):X@p.D;}
~-----------
~mut p.A:{'this .id[X:imm](_:p.Box[X]):X}
~mut p.Box[K:imm]:{'this .get:K}
~mut p.C:{'this .id[Y:imm](_:p.Box[Y]):Y}
~mut p.D:p.A, p.C{'this .id[X:imm](_:p.Box[X]):X}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X:imm](x:Box[X]):X}
C:{.id[Y:imm](y:Box[Y]):Y}
D:A,C{}
"""));
}

@Test void inferAlpha_DefaultImplVsAbstract_PickAlignedImpl(){ okI("""
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.Box[K:imm]:{'this .get:K@p.Box;}
p.C:{'this .id[Y:imm](p.Box[Y]):Y@p.C;(y)->y:?.get():?;}
p.D:p.A, p.C{'this .id[X:imm](p.Box[X]):X@p.C;}
~-----------
~mut p.A:{'this .id[X:imm](_:p.Box[X]):X}
~mut p.Box[K:imm]:{'this .get:K}
~mut p.C:{'this .id[Y:imm](y:p.Box[Y]):Y->y.get[imm]}
~mut p.D:p.A, p.C{'this .id[X:imm](_:p.Box[X]):X}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X](x:Box[X]):X}
C:{.id[Y](y:Box[Y]):Y->y.get} // has impl
D:A,C{} // merge supertypes; impl origin is in C after alignment
"""));
}
//Not double checked after change in print style. What was this checking?
@Test void abcd(){okI("""
p.Any:{'this ![T:imm]:T@p.Any;->p.Any:?![T]():?;}
p.Baba[C:imm, D:imm]:p.GG[p.Any,p.Any]{'this .apply[_AC:imm,_AD:imm](p.Any,p.Any,_AC):_AD@p.GG;}
p.GG[A:imm, B:imm]:{'this .apply[C:imm,D:imm](A,B,C):D@p.GG;}
p.KK:{'_ .k[K:imm]:K@p.KK;->this:?.withGG[C,D](p._BUser:$?{'_ ? [?](?,?,?):?@!;(a, b, c)->p.Any:?!():?;}:?):?;}
p.User:{'this .withGG[A1:imm,B1:imm](p.GG[A1,B1]):p.User@p.User; .foo1[C:imm,D:imm]:p.User@p.User;->this:?.withGG[C,D](p._AUser:$?{'_ ? [?](?,?,?):?@!;(a, b, c)->p.Any:?!():?;}:?):?; .foo2[C:imm,D:imm]:p.User@p.User;->p.KK:{'_ ? .k[K:imm]:K@!;->this:?.withGG[C,D](p._BUser:$?{'_ ? [?](?,?,?):?@!;(a, b, c)->p.Any:?!():?;}:?):?;}:?.k[p.User]():?;}
p._AUser[C:imm, D:imm]:p.GG[imm C,imm D]{'_ .apply[_AC:imm,_AD:imm](imm C,imm D,_AC):_AD@p._AUser;(a, b, c)->p.Any:p.Any![imm,?]():_AD;}
p._BUser[C:imm, D:imm]:p.GG[imm C,imm D]{'_ .apply[_BC:imm,_BD:imm](imm C,imm D,_BC):_BD@p._BUser;(a, b, c)->p.Any:p.Any![imm,?]():_BD;}
~-----------
~mut p.Any:{'this ![T:imm]:T->p.Any![imm,T]}
~mut p.Baba[C:imm,D:imm]:p.GG[p.Any,p.Any]{'this .apply[_AC:imm,_AD:imm](_:p.Any, _:p.Any, _:_AC):_AD}
~mut p.GG[A:imm,B:imm]:{'this .apply[C:imm,D:imm](_:A, _:B, _:C):D}
~mut p.User:{'this .withGG[A1:imm,B1:imm](_:p.GG[A1,B1]):p.User; .foo1[C:imm,D:imm]:p.User->this.withGG[imm,C,D](imm p._AUser[C:imm,D:imm]:p.GG[imm C,imm D]{'_ .apply[_AC:imm,_AD:imm](a:imm C, b:imm D, c:_AC):_AD->p.Any![imm,imm _AD]}); .foo2[C:imm,D:imm]:p.User->imm p.KK:{'_ .k[K:imm]:K->this.withGG[imm,C,D](imm p._BUser[C:imm,D:imm]:p.GG[imm C,imm D]{'_ .apply[_BC:imm,_BD:imm](a:imm C, b:imm D, c:_BC):_BD->p.Any![imm,imm _BD]})}.k[imm,p.User]}
""", List.of("""
GG[A,B]:{ .apply[C,D](A,B,C):D }
Baba[C,D]:GG[Any,Any]{}
Any:{![T]:T->Any![T]}
User:{
  .withGG[A1,B1](GG[A1,B1]):User;
  .foo1[C,D]:User->this.withGG[C,D]({a,b,c->Any!});
  .foo2[C,D]:User->KK:{ .k[K]:K->this.withGG[C,D]({a,b,c->Any!})}.k[User];
}
"""));}
@Test void inferAlpha_GenericMethod_LambdaImplements_Generic_OverrideDifferentNames(){okI("""
p.A:{'this .use[X1:imm,Y1:imm](X1,p.Conv):Y1@p.A;}
p.B:p.A{'this .use[U1:imm,V1:imm](U1,p.Conv):V1@p.B;(x, c)->c:?.apply[U1,V1](x:?):?;}
p.Conv:{'this .apply[S1:imm,S2:imm](S1):S2@p.Conv;}
~-----------
~mut p.A:{'this .use[X1:imm,Y1:imm](_:X1, _:p.Conv):Y1}
~mut p.B:p.A{'this .use[U1:imm,V1:imm](x:U1, c:p.Conv):V1->c.apply[imm,U1,V1](x)}
~mut p.Conv:{'this .apply[S1:imm,S2:imm](_:S1):S2}
""", List.of("""
Conv:{ .apply[S1,S2](s:S1):S2 }
A:{ .use[X1,Y1](x:X1,c:Conv):Y1 }
B:A{
  .use[U1,V1](x:U1,c:Conv):V1 -> c.apply[U1,V1](x)
}
"""));}

@Test void boundMustAlphaSimple(){okI("""
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1[X:imm]:p.A{'this .m[_AX:imm](p.Foo[_AX]):_AX@p.B1;(z)->z:?.get():?;}
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
~-----------
~mut p.A:{'this .m[X:imm](_:p.Foo[X]):X}
~mut p.B1[X:imm]:p.A{'this .m[_AX:imm](z:p.Foo[_AX]):_AX->z.get[imm]}
~mut p.Foo[K:imm]:{'this .get:K; .beer[G:imm]:G}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1[X]:A{.m(z)->z.get}
"""));}

@Test void inLineAnonObject1(){okI("""
[###]~-----------
~mut p.User:{'this\
 .m:p.User->imm p.Bla:{'_ .bla:p.User->p.User}.bla[imm]}
""",List.of("""
User:{.m:User->
 Bla:{.bla:User->User;}.bla
}
"""));}

@Test void inLineAnonObject2(){okI("""
[###]~-----------
~mut p.User:{'this .m:p.User->imm p._AUser:p.User{'_ .bla:p.User->p.User; .m:p.User}.bla[imm]}
""",List.of("""
User:{.m:User->
 {.bla:User->User;}.bla
}
"""));}

@Test void regressionMethodHeaderAndGet1(){okI("""
p.A:{'this}
p.User:{'this .m:p.A@p.User;->p._AUser:$?{'_ ? .m[?]:p.A@!;->p.A:?;}:?;}
p._AUser:p.A{'_ .m:p.A@p._AUser;->p.A:p.A;}
~-----------
~mut p.A:{'this }
~mut p.User:{'this .m:p.A->imm p._AUser:p.A{'_ .m:p.A->p.A}}
""",List.of("""
A:{}
User:{ .m:A->{ .m:A->A;}; }
"""));}

@Test void regressionMethodHeaderAndGet2(){failI("""
In file: [###]/in_memory0.fear

003| User:{ .m:A->{ .m->A;}; }
   |              --^^^^^--

While inspecting object literal instance of "A"
Cannot infer signature of method ".m".
No supertype has a method named ".m" with 0 parameters.
Error 9 WellFormedness
""",List.of("""
A:{}
User:{ .m:A->{ .m->A;}; }
"""));}

@Test void badSealedOutNoInference(){failI("""
In file: [###]/in_memory0.fear

003| User:base.Void{ .m:A->A }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "User"
Type declaration "User" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type declaration "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",List.of("""
A:{}
User:base.Void{ .m:A->A }
"""));}

@Test void badSealedOutEmpty(){failI("""
In file: [###]/in_memory0.fear

003| User:base.Void{ .foo:A }
   | ^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "User"
Type declaration "User" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type declaration "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",List.of("""
A:{}
User:base.Void{ .foo:A }
"""));}

@Test void badSealedOutInferenceUsed(){failI("""
In file: [###]/in_memory0.fear

003| User:Void{ .m:A->A }
   | ^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "User"
Type declaration "User" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type declaration "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",importMini,List.of("""
A:{}
User:Void{ .m:A->A }
"""));}

@Test void badSealedOutInferenceInner(){failI("""
In file: [###]/in_memory0.fear

003| User:{ .m:base.Void->{ .m:A->A;}; }
   |                      ^^^^^^^^^^^

While inspecting object literal instance of "base.Void"
Object literal instance of "base.Void" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal instance of "base.Void" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",List.of("""
A:{}
User:{ .m:base.Void->{ .m:A->A;}; }
"""));}

//This instead should pass, to allow True/False as values
//Note how it seem to go to p._AUser:$?:? in the middle.
//Correct since the user specified {}
@Test void sealedOutInferenceInnerEmpty(){okI("""
p.A:{'this}
p.User:{'this .m:base.Void@p.User;->p._AUser:$?:?;}
~-----------
~mut p.A:{'this }
~mut p.User:{'this .m:base.Void->base.Void}
""",List.of("""
A:{}
User:{ .m:base.Void->{ }; }
"""));}
//This would not compile, but this test is about inference only
@Test void sealedOutInferenceInnerEmptyExplicit(){okI("""
p.A:{'this}
p.User:{'this .m:base.Void@p.User;->base.Block:?;}
~-----------
~mut p.A:{'this }
~mut p.User:{'this .m:base.Void->base.Block}
""",List.of("""
A:{}
User:{ .m:base.Void->base.Block; }
"""));}


@Test void expandDeclarationStages(){okI("""
p.A:{'this .m:base.Nat@p.A;->base.1:?;}
p.B:p.A{'this .m:base.Nat@p.B;->base.2:?;}
p.C:p.B, p.A{'this .m:base.Nat@p.B;}
~-----------
~mut p.A:{'this .m:base.Nat->base.1}
~mut p.B:p.A{'this .m:base.Nat->base.2}
~mut p.C:p.B, p.A{'this .m:base.Nat}
""",List.of("""
A: { .m():base.Nat -> 1; }
B:A{ .m():base.Nat -> 2; }
C:B{}
"""));}

//The Err below is ok, associated to t:Err and not impacting the method signature
//it is produced by subtype read/imm T > T not being considered
@Test void genericInterfaces(){okI("""
p.Box[T:imm,mut,read]:{'this mut .expose:T@p.Box; read .get:read/imm T@p.Box;}
p.MakeBox:{'this #[T:imm,mut,read](T):mut p.Box[T]@p.MakeBox;(t)->p._AMake:$?{'_ ? .expose[?]:?@!;->t:?; ? .get[?]:?@!;->t:?;}:?;}
p.MyB:p.Box[p.MakeBox]{'this .foo:p.MyB@p.MyB;->p._AMyB:$?:?; mut .expose:p.MakeBox@p.Box; read .get:p.MakeBox@p.Box;}
p._AMake[T:imm,mut,read]:p.Box[T]{'_ mut .expose:T@p._AMake;->t:T; read .get:read/imm T@p._AMake;->t:T;}
~-----------
~mut p.Box[T:imm,mut,read]:{'this mut .expose:T; read .get:read/imm T}
~mut p.MakeBox:{'this #[T:imm,mut,read](t:T):mut p.Box[T]->mut p._AMake[T:imm,mut,read]:p.Box[T]{'_ mut .expose:T->t; read .get:read/imm T->t}}
~mut p.MyB:p.Box[p.MakeBox]{'this .foo:p.MyB->p.MyB; mut .expose:p.MakeBox; read .get:p.MakeBox}
""",List.of("""
Box[T:*]:{
  mut .expose:T;
  read .get: read/imm T;
}
MakeBox:{#[T:*](t:T):mut Box[T]->{.expose->t; .get->t}}
MyB:Box[MakeBox]{ .foo:MyB->{}}
"""));}
//The results below are actually correct: the method stays read/imm X if not overridden by user.
//Overriding would work since it is subtype indeed.
@Test void genericInterfacesImpl(){okI("""
p.A1:p.Box[p.MakeBox]{'this mut .expose:p.MakeBox@p.Box; read .get:p.MakeBox@p.Box;}
p.A2[X:imm]:p.Box[X]{'this mut .expose:X@p.Box; read .get:read/imm X@p.Box;}
p.A3[X:mut]:p.Box[X]{'this mut .expose:X@p.Box; read .get:read/imm X@p.Box;}
p.A4[X:read]:p.Box[X]{'this mut .expose:X@p.Box; read .get:read/imm X@p.Box;}
p.Box[###]
p.MakeBox:[###]
p._AMake[T:imm,mut,read]:p.Box[T]{'_ mut .expose:T@p._AMake;->t:T; read .get:read/imm T@p._AMake;->t:T;}
~-----------
~mut p.A1:p.Box[p.MakeBox]{'this mut .expose:p.MakeBox; read .get:p.MakeBox}
~mut p.A2[X:imm]:p.Box[X]{'this mut .expose:X; read .get:read/imm X}
~mut p.A3[X:mut]:p.Box[X]{'this mut .expose:X; read .get:read/imm X}
~mut p.A4[X:read]:p.Box[X]{'this mut .expose:X; read .get:read/imm X}
~mut p.Box[T:imm,mut,read]:{'this mut .expose:T; read .get:read/imm T}
~mut p.MakeBox:{'this #[T:imm,mut,read](t:T):mut p.Box[T]->mut p._AMake[T:imm,mut,read]:p.Box[T]{'_ mut .expose:T->t; read .get:read/imm T->t}}
""",List.of("""
Box[T:*]:{
  mut .expose:T;
  read .get: read/imm T;
}
MakeBox:{#[T:*](t:T):mut Box[T]->{.expose->t; .get->t}}

A1:Box[MakeBox]{ }
A2[X:imm]:Box[X]{ }
A3[X:mut]:Box[X]{ }
A4[X:read]:Box[X]{ }
"""));}

@Test void typeRenamePath(){ okI("""
p.Box[T:imm,mut,read]:{'this}
p.User:{'this read .idX[X:imm](X):X@p.User; read .idReadX[X:imm](X):read/imm X@p.User; read .idBox[X:imm](X):p.Box[X]@p.User;}
~-----------
~mut p.Box[T:imm,mut,read]:{'this }
~mut p.User:{'this read .idX[X:imm](_:X):X; read .idReadX[X:imm](_:X):read/imm X; read .idBox[X:imm](_:X):p.Box[X]}
""", List.of("""
Box[T:*]:{
}
User:{'this
  read .idX[X:imm](x:X):X;
  read .idReadX[X:imm](x:X):read/imm X;
  read .idBox[X:imm](x:X):Box[X];
}
"""));}

@Test void overloadNorm_receivers_basic(){okI("""
p.A:{'this .a:p.A@p.A;->p.A:?; read .a:p.A@p.A;->p.A:?; mut .a:p.A@p.A;->p.A:?;}
p.IdUser:{'this .m1(p.A):p.A@p.IdUser;(x)->x:?.a():?; .m2(read p.A):p.A@p.IdUser;(x)->x:?.a():?; .m3(mut p.A):p.A@p.IdUser;(x)->x:?.a():?; .m4(iso p.A):p.A@p.IdUser;(x)->x:?.a():?; .m5(readH p.A):p.A@p.IdUser;(x)->x:?.a():?; .m6(mutH p.A):p.A@p.IdUser;(x)->x:?.a():?;}
~-----------
~mut p.A:{'this .a:p.A->p.A; read .a:p.A->p.A; mut .a:p.A->p.A}
~mut p.IdUser:{'this\
 .m1(x:p.A):p.A->x.a[imm];\
 .m2(x:read p.A):p.A->x.a[read];\
 .m3(x:mut p.A):p.A->x.a[mut];\
 .m4(x:iso p.A):p.A->x.a[mut];\
 .m5(x:readH p.A):p.A->x.a[read];\
 .m6(x:mutH p.A):p.A->x.a[mut]}
""",
  List.of("""
A:{
  imm .a:A->A;
  read .a:A->A;
  mut .a:A->A; 
}
IdUser:{
  .m1(x:imm A):A->x.a;
  .m2(x:read A):A->x.a;
  .m3(x:mut A):A->x.a;
  .m4(x:iso A):A->x.a;
  .m5(x:readH A):A->x.a;
  .m6(x:mutH A):A->x.a;
}
"""));}

//Here we declare absorb as taking zero args.
//Thus, we can not infer # generics, the method does not exists.
//TODO: this needs to move to type system and have a good error there
@Test void usesLocalTypeForInferenceBadArgCount(){okI("""
p.Absorb:{'this #[T:imm]:base.Void@p.Absorb;->base.Void:?;}
p.Foo:{'this .m:p.Point@p.Foo;->p.Point:{'_ ? .x[?]:base.Nat@!;->base.0:?; ? .y[?]:base.Nat@!;->base.0:?;}:?;}
p.Point:{'_ .x:base.Nat@p.Point;->base.0:?; .y:base.Nat@p.Point;->base.0:?;}
p.User1:{'this .bla(p.Point):base.Void@p.User1;(p)->p.Absorb:?#(p:?):?;}
p.User2:{'this .bla(p.Point):base.Void@p.User2;(p)->p.Absorb:?#(p:?.x():?):?;}
~-----------
~mut p.Absorb:{'this #[T:imm]:base.Void->base.Void}
~mut p.Foo:{'this .m:p.Point->imm p.Point:{'_ .x:base.Nat->base.0; .y:base.Nat->base.0}}
~mut p.User1:{'this .bla(p:p.Point):base.Void->p.Absorb#[imm](p)}
~mut p.User2:{'this .bla(p:p.Point):base.Void->p.Absorb#[imm](p.x[imm])}
""",List.of("""
Foo:{ .m : Point -> Point:{ .x:base.Nat->0; .y:base.Nat->0;} }
Absorb:{ #[T]:base.Void -> base.Void; }
User1:{ .bla(p:Point):base.Void -> Absorb#p; }
User2:{ .bla(p:Point):base.Void -> Absorb#(p.x); }
"""));}

@Test void usesLocalTypeForInference(){okI("""
[###]~-----------
~mut p.Absorb:{'this #[T:imm](_:T):base.Void->base.Void}
~mut p.Foo:{'this .m:p.Point->imm p.Point:{'_ .x:base.Nat->base.0; .y:base.Nat->base.0}}
~mut p.User1:{'this .bla(p:p.Point):base.Void->p.Absorb#[imm,p.Point](p)}
~mut p.User2:{'this .bla(p:p.Point):base.Void->p.Absorb#[imm,base.Nat](p.x[imm])}
""",List.of("""
Foo:{ .m : Point -> Point:{ .x:base.Nat->0; .y:base.Nat->0;} }
Absorb:{ #[T](T):base.Void -> base.Void; }
User1:{ .bla(p:Point):base.Void -> Absorb#p; }
User2:{ .bla(p:Point):base.Void -> Absorb#(p.x); }
"""));}

//TODO: this correctly shows that we can override a user defined type
//.beer[imm,X] becomes .beer[imm,Err]
//we will then merge back the user defined types when creating the core 
@Test void boundMustAlpha(){okI("""
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1[X:imm]:p.A{'this .m[_AX:imm](p.Foo[_AX]):_AX@p.B1;(z)->z:?.get():?;}
p.B2[X:imm]:p.A{'this .m[_AX:imm](p.Foo[_AX]):_AX@p.B2;(z)->z:?.beer[X]():?;}
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
~-----------
~mut p.A:{'this .m[X:imm](_:p.Foo[X]):X}
~mut p.B1[X:imm]:p.A{'this .m[_AX:imm](z:p.Foo[_AX]):_AX->z.get[imm]}
~mut p.B2[X:imm]:p.A{'this .m[_AX:imm](z:p.Foo[_AX]):_AX->z.beer[imm,X]}
~mut p.Foo[K:imm]:{'this .get:K; .beer[G:imm]:G}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1[X]:A{.m(z)->z.get}
B2[X]:A{.m(z)->z.beer[X]}
"""));}
//The above could be solved by comparing the input and the result on the top level inference steps.
//arguably, this could be applied when making the transition inference->core
//TODO: when committing to class table consider replacing all the bodies with Void or Magic! to avoid worst case shenario quadratic memory consumption.


@Test void recoverUserTypes1(){okI("""
[###]~-----------
~mut p.A:p.I{'this }
~mut p.B:p.I{'this }
~mut p.Foo:{'this .get[T:imm](a:T, b:T):T->a}
~mut p.I:{'this }
~mut p.User:{'this .m:p.I->p.Foo.get[imm,p.A](p.A, p.B)}
""",List.of("""
I:{}
A:I{}
B:I{}
Foo:{.get[T](a:T,b:T):T->a;}
User:{.m:I->Foo.get(A,B)}
"""));}
//But here we should keep the user specified type 
@Test void recoverUserTypes2(){okI("""
[###]~-----------
~mut p.A:p.I{'this }
~mut p.B:p.I{'this }
~mut p.Foo:{'this .get[T:imm](a:T, b:T):T->a}
~mut p.I:{'this }
~mut p.User:{'this .m:p.I->p.Foo.get[imm,p.I](p.A, p.B)}
""",List.of("""
I:{}
A:I{}
B:I{}
Foo:{.get[T](a:T,b:T):T->a;}
User:{.m:I->Foo.get[I](A,B)}
"""));}


@Test void regressionOnMethGen0(){okI("""
[###]~-----------
~mut p.Any:{'this #[T:imm,mut,read]:T->p.Any#[imm,T]}
~mut p.BlockQ[R5:imm,mut,read]:{'this mut .loop(body:mut p.ControlFlowQ[R5]):mut p.BlockQ[R5]->body.match[mut,mut p.BlockQ[R5]](mut p._ABloc[R5:imm,mut,read]:p.ControlFlowMatchQ[R5,mut p.BlockQ[R5]]{'_ mut .return(rv:R5):mut p.BlockQ[R5]->p.Any#[imm,mut p.BlockQ[R5]]})}
~mut p.ControlFlowMatchQ[T:imm,mut,read,R4:imm,mut,read]:{'this mut .return(_:T):R4}
~mut p.ControlFlowQ:{'this .return[T:imm,mut,read](returnValue:T):mut p.ControlFlowQ[T]->this.return[imm,T](returnValue)}
~mut p.ControlFlowQ[T:imm,mut,read]:{'this mut .match[R3:imm,mut,read](m:mut p.ControlFlowMatchQ[T,R3]):R3->m.return[mut](p.Any#[imm,T])}
~mut p.LoopBodyQ[R2:imm,mut,read]:p.ReturnStmtQ[mut p.ControlFlowQ[R2]]{'this mut #:mut p.ControlFlowQ[R2]}
~mut p.ReturnStmtQ[R1:imm,mut,read,iso]:{'this mut #:R1}
""",List.of("""
Any:{#[T:*]:T->Any#[imm,T]}
ReturnStmtQ[R1:iso,imm,mut,read]: {mut #: R1}
LoopBodyQ[R2:*]: ReturnStmtQ[mut ControlFlowQ[R2]]{}
ControlFlowQ: {
  .return[T:*](returnValue: T): mut ControlFlowQ[T] -> this.return(returnValue);
  }
ControlFlowQ[T:*]: {
  mut .match[R3:*](m: mut ControlFlowMatchQ[T,R3]): R3 -> m.return(Any#);
  }
ControlFlowMatchQ[T:*,R4:*]: {
  mut .return(returnValue: T): R4;
  }
BlockQ[R5:*]: {
  mut .loop(body: mut ControlFlowQ[R5]): mut BlockQ[R5] -> body.match{
    .return(rv) -> Any#;
    };
  }
"""));}

@Test void regressionOnMethGen1(){okI("""
[###]~-----------
~mut p.Any:{'this #[T:imm,mut,read]:T->p.Any#[imm,T]}
~mut p.BlockQ[R5:imm,mut,read]:{'this mut .loop(body:mut p.LoopBodyQ[R5]):mut p.BlockQ[R5]->body#[mut].match[mut,mut p.BlockQ[R5]](mut p._ABloc[R5:imm,mut,read]:p.ControlFlowMatchQ[R5,mut p.BlockQ[R5]]{'_ mut .return(rv:R5):mut p.BlockQ[R5]->p.Any#[imm,mut p.BlockQ[R5]]})}
~mut p.ControlFlowMatchQ[T:imm,mut,read,R4:imm,mut,read]:{'this mut .return(_:T):R4}
~mut p.ControlFlowQ:{'this .return[T:imm,mut,read](returnValue:T):mut p.ControlFlowQ[T]->this.return[imm,T](returnValue)}
~mut p.ControlFlowQ[T:imm,mut,read]:{'this mut .match[R3:imm,mut,read](m:mut p.ControlFlowMatchQ[T,R3]):R3->m.return[mut](p.Any#[imm,T])}
~mut p.LoopBodyQ[R2:imm,mut,read]:p.ReturnStmtQ[mut p.ControlFlowQ[R2]]{'this mut #:mut p.ControlFlowQ[R2]}
~mut p.ReturnStmtQ[R1:imm,mut,read,iso]:{'this mut #:R1}
""",List.of("""
Any:{#[T:*]:T->Any#[imm,T]}
ReturnStmtQ[R1:iso,imm,mut,read]: {mut #: R1}
LoopBodyQ[R2:*]: ReturnStmtQ[mut ControlFlowQ[R2]]{}
ControlFlowQ: {
  .return[T:*](returnValue: T): mut ControlFlowQ[T] -> this.return(returnValue);
  }
ControlFlowQ[T:*]: {
  mut .match[R3:*](m: mut ControlFlowMatchQ[T,R3]): R3 -> m.return(Any#);
  }
ControlFlowMatchQ[T:*,R4:*]: {
  mut .return(returnValue: T): R4;
  }
BlockQ[R5:*]: {
  mut .loop(body: mut LoopBodyQ[R5]): mut BlockQ[R5] -> body#.match{
    .return(rv) -> Any#;
    };
  }
"""));}

@Test void regressionOnMethGen2(){okI("""
[###]~-----------
~mut p.Any:{'this #[T:imm]:T->p.Any#[imm,T]}
~mut p.Block:{'this #[R3:imm,mut,read]:mut p.Block[R3]->mut p.Block[R3]; #[X:imm,mut,read,iso,mutH,readH](x:X):base.Void->base.Void; #[X:imm,mut,read,iso,mutH,readH,R3:imm,mut,read,iso,mutH,readH](_:X, res:R3):R3->res; #[X1:imm,mut,read,iso,mutH,readH,X2:imm,mut,read,iso,mutH,readH,R3:imm,mut,read,iso,mutH,readH](_:X1, _:X2, res:R3):R3->res; #[X1:imm,mut,read,iso,mutH,readH,X2:imm,mut,read,iso,mutH,readH,X3:imm,mut,read,iso,mutH,readH,R3:imm,mut,read,iso,mutH,readH](_:X1, _:X2, _:X3, res:R3):R3->res; #[X1:imm,mut,read,iso,mutH,readH,X2:imm,mut,read,iso,mutH,readH,X3:imm,mut,read,iso,mutH,readH,X4:imm,mut,read,iso,mutH,readH,R3:imm,mut,read,iso,mutH,readH](_:X1, _:X2, _:X3, _:X4, res:R3):R3->res}
~mut p.BlockIf[R2:imm,mut,read]:{'this mut .return(_:mut p.ReturnStmt[R2]):mut p.Block[R2]; mut .do(_:mut p.ReturnStmt[base.Void]):mut p.Block[R2]}
~mut p.Block[R:imm,mut,read]:{'this mut .done:base.Void->base.Void; mut .return(a:mut p.ReturnStmt[R]):R->a#[mut]; mut .do(r:mut p.ReturnStmt[base.Void]):mut p.Block[R]->this._do[mut](r#[mut]); mut ._do(v:base.Void):mut p.Block[R]->this; mut .let[X:imm,mut,read](x:mut p.ReturnStmt[X], cont:mut p.Continuation[X,mut p.Block[R],R]):R->cont#[mut](x#[mut], this); mut .openIso[X:imm,mut,read,iso](x:iso X, cont:mut p.Continuation[mut X,mut p.Block[R],R]):R->cont#[mut](x, this); mut .if(p:mut p.Condition):mut p.BlockIf[R]->p#[mut]?[imm,mut p.BlockIf[R]](mut p._FBloc[R:imm,mut,read]:base.ThenElse[mut p.BlockIf[R]]{'cond mut .then:mut p.BlockIf[R]->mut p._DBloc[R:imm,mut,read]:p.BlockIf[R]{'t mut .return(a:mut p.ReturnStmt[R]):mut p.Block[R]->p._DecidedBlock#[imm,R](a#[mut]); mut .do(r:mut p.ReturnStmt[base.Void]):mut p.Block[R]->t._do[mut](r#[mut]); mut ._do(v:base.Void):mut p.Block[R]->this}; mut .else:mut p.BlockIf[R]->mut p._EBloc[R:imm,mut,read]:p.BlockIf[R]{'f mut .return(_:mut p.ReturnStmt[R]):mut p.Block[R]->this; mut .do(_:mut p.ReturnStmt[base.Void]):mut p.Block[R]->this}}); mut .loop(body:mut p.LoopBody[R]):mut p.Block[R]->body#[mut].match[mut,mut p.Block[R]](mut p._GBloc[R:imm,mut,read]:p.ControlFlowMatch[R,mut p.Block[R]]{'_ mut .continue:mut p.Block[R]->this.loop[mut](body); mut .break:mut p.Block[R]->this; mut .return(rv:R):mut p.Block[R]->p._DecidedBlock#[imm,R](rv)})}
~mut p.Condition:p.ReturnStmt[base.Bool]{'this mut #:base.Bool}
~mut p.Continuation[T:imm,mut,read,C:imm,mut,read,R:imm,mut,read]:{'this mut #(_:T, _:C):R}
~mut p.ControlFlow:{'this .continue:mut p.ControlFlow[base.Void]->mut p.ControlFlowContinue:p.ControlFlow[base.Void]{'_ mut .match[R:imm,mut,read](m:mut p.ControlFlowMatch[base.Void,R]):R->m.continue[mut]}; .break:mut p.ControlFlow[base.Void]->mut p.ControlFlowBreak:p.ControlFlow[base.Void]{'_ mut .match[R:imm,mut,read](m:mut p.ControlFlowMatch[base.Void,R]):R->m.break[mut]}; .continueWith[T:imm,mut,read]:mut p.ControlFlow[T]->mut p.ControlFlowContinue[T:imm,mut,read]:p.ControlFlow[T]{'_ mut .match[R:imm,mut,read](m:mut p.ControlFlowMatch[T,R]):R->m.continue[mut]}; .breakWith[T:imm,mut,read]:mut p.ControlFlow[T]->mut p.ControlFlowBreak[T:imm,mut,read]:p.ControlFlow[T]{'_ mut .match[R:imm,mut,read](m:mut p.ControlFlowMatch[T,R]):R->m.break[mut]}; .return[T:imm,mut,read](returnValue:T):mut p.ControlFlow[T]->mut p.ControlFlowReturn[T:imm,mut,read]:p.ControlFlow[T]{'_ mut .match[R:imm,mut,read](m:mut p.ControlFlowMatch[T,R]):R->m.return[mut](returnValue); mut .value:T->returnValue}}
~mut p.ControlFlowMatch[T:imm,mut,read,R4:imm,mut,read]:{'this mut .continue:R4; mut .break:R4; mut .return(_:T):R4}
~mut p.ControlFlow[T:imm,mut,read]:{'this mut .match[R:imm,mut,read](m:mut p.ControlFlowMatch[T,R]):R->m.continue[mut]}
~mut p.LoopBody[R:imm,mut,read]:p.ReturnStmt[mut p.ControlFlow[R]]{'this mut #:mut p.ControlFlow[R]}
~mut p.ReturnStmt[R:imm,mut,read,iso]:{'this mut #:R}
~mut p._DecidedBlock:{'this #[R1:imm,mut,read](res:R1):mut p.Block[R1]->mut p._BDeci[R1:imm,mut,read]:p.Block[R1]{'self mut .return(_:mut p.ReturnStmt[R1]):R1->res; mut .do(_:mut p.ReturnStmt[base.Void]):mut p.Block[R1]->self; mut .let[X:imm,mut,read](_:mut p.ReturnStmt[X], _:mut p.Continuation[X,mut p.Block[R1],R1]):R1->res; mut .openIso[X:imm,mut,read,iso](_:iso X, _:mut p.Continuation[mut X,mut p.Block[R1],R1]):R1->res; mut .if(_:mut p.Condition):mut p.BlockIf[R1]->mut p._ADeci[R1:imm,mut,read]:p.BlockIf[R1]{'_ mut .return(_:mut p.ReturnStmt[R1]):mut p.Block[R1]->self; mut .do(_:mut p.ReturnStmt[base.Void]):mut p.Block[R1]->self}; mut .loop(_:mut p.LoopBody[R1]):mut p.Block[R1]->self; mut .done:base.Void; mut ._do(_:base.Void):mut p.Block[R1]}}
""","role app000; use base.Void as Void; use base.Bool as Bool;",List.of("""
Any:{#[T]:T->Any#[imm,T]}
ReturnStmt[R:iso,imm,mut,read]: {mut #: R}
Condition: ReturnStmt[Bool]{}
LoopBody[R:*]: ReturnStmt[mut ControlFlow[R]]{}
Continuation[T:*,C:*,R:*]: {mut #(x: T, self: C): R}
ControlFlow: {
  .continue: mut ControlFlow[Void] -> mut ControlFlowContinue: ControlFlow[Void]{.match(m) -> m.continue};
  .break: mut ControlFlow[Void] -> mut ControlFlowBreak: ControlFlow[Void]{.match(m) -> m.break};
  .continueWith[T:*]: mut ControlFlow[T] ->  mut ControlFlowContinue[T:*]: ControlFlow[T]{.match(m) -> m.continue};
  .breakWith[T:*]: mut ControlFlow[T] -> mut ControlFlowBreak[T:*]: ControlFlow[T]{.match(m) -> m.break};
  .return[T:*](returnValue: T): mut ControlFlow[T] -> mut ControlFlowReturn[T:*]: ControlFlow[T]{
    .match(m) -> m.return(returnValue);
    mut .value: T -> returnValue;
    };
  }
ControlFlow[T:*]: {//This caused a comparision between R and mut Block[R]
  mut .match[R:*](m: mut ControlFlowMatch[T,R]): R -> m.continue;
  }
/*ControlFlow[T:*]: {//This does not
  mut .match[R5:*](m: mut ControlFlowMatch[T,R5]): R5 -> m.continue;
  }*/
ControlFlowMatch[T:*,R4:*]: {
  mut .continue: R4;
  mut .break: R4;
  mut .return(returnValue: T): R4;
  }
Block:{
  #[R3:*]: mut Block[R3] -> {};
  #[X:**](x: X): Void -> {};
  #[X:**, R3:**](_: X, res: R3): R3 -> res;
  #[X1:**, X2:**, R3:**](_: X1, _: X2, res: R3): R3 -> res;
  #[X1:**, X2:**, X3:**, R3:**](_: X1, _: X2, _: X3, res: R3): R3 -> res;
  #[X1:**, X2:**, X3:**, X4:**, R3:**](_: X1, _: X2, _: X3, _: X4, res: R3): R3 -> res;
  }
Block[R:*]: {
  mut .done: Void -> {};
  mut .return(a: mut ReturnStmt[R]): R -> a#;
  mut .do(r: mut ReturnStmt[Void]): mut Block[R] -> this._do(r#);
    mut ._do(v: Void): mut Block[R] -> this;
  mut .let[X:*](
    x: mut ReturnStmt[X],
    cont: mut Continuation[X, mut Block[R], R]
    ): R ->
      cont#(x#, this);
  mut .openIso[X:iso,imm,mut,read](
    x: iso X,
    cont: mut Continuation[mut X, mut Block[R], R]
    ): R ->
      cont#(x, this);
  mut .if(p: mut Condition): mut BlockIf[R] -> p# ? { 'cond
    .then -> { 't
      .return(a) -> _DecidedBlock#(a#);
      .do(r) -> t._do[](r#);
        mut ._do(v: Void): mut Block[R] -> this;
      };
    .else -> { 'f
      .return(_) -> this;
      .do(_) -> this;
      };
    };
  mut .loop(body: mut LoopBody[R]): mut Block[R] -> body#.match{
    .continue -> this.loop(body);
    .break -> this;
    .return(rv) -> _DecidedBlock#rv;
    };
  }
BlockIf[R2:*]:{
  mut .return(a: mut ReturnStmt[R2]): mut Block[R2];
  mut .do(r: mut ReturnStmt[Void]): mut Block[R2];
  }
_DecidedBlock:{
  #[R1:*](res: R1): mut Block[R1] -> { 'self
    .return(_) -> res;
    .do(_) -> self;
    .let(_, _) -> res;
    .openIso(_, _) -> res;
    .if(_) -> {
      .return(_) -> self;
      .do(_) -> self;
      };
  .loop(_) -> self;
  }
}
"""));}

@Test void boundHiding1(){okI("""
p.Box[X:imm,mut,read]:{'this mut .f[R:imm,mut,read](X):R@p.Box;}
p.Dool:{'this}
p.User:{'this mut .go[R:imm,mut,read](mut p.Box[R],R):p.Dool@p.User;(b, x)->b:?.f(x:?):?;}
~-----------
~mut p.Box[X:imm,mut,read]:{'this mut .f[R:imm,mut,read](_:X):R}
~mut p.Dool:{'this }
~mut p.User:{'this mut .go[R:imm,mut,read](b:mut p.Box[R], x:R):p.Dool->b.f[mut,p.Dool](x)}
""",List.of("""
Dool:{}
Box[X:*]:{ mut .f[R:*](x: X): R }
User:{
  mut .go[R:*](b: mut Box[R], x: R): Dool -> b.f(x);
}
"""));}

@Test void boundHiding2(){okI("""
p.Any:{'this #[T:imm]:T@p.Any;}
p.Box[X:imm,mut,read]:{'this .f[R:imm,mut,read](p.F[X,X,R]):R@p.Box;}
p.Dool:{'this}
p.F[A:imm, B:imm, C:imm]:{'this #(A,B):C@p.F;}
p.User:{'this mut .go1[R:imm,mut,read](p.Box[R]):p.Dool@p.User;(b)->b:?.f(p._AUser:$?{'_ ? [?](?,?):?@!;(aa, bb)->p.Any:?#():?;}:?):?; mut .go2(p.Box[p.User]):p.Dool@p.User;(b)->b:?.f(p._BUser:$?{'_ ? [?](?,?):?@!;(aa, bb)->p.Any:?#():?;}:?):?;}
p._AUser[R:imm,mut,read]:p.F[imm R,imm R,p.Dool]{'_ #(imm R,imm R):p.Dool@p._AUser;(aa, bb)->p.Any:p.Any#[imm,?]():p.Dool;}
p._BUser:p.F[p.User,p.User,p.Dool]{'_ #(p.User,p.User):p.Dool@p._BUser;(aa, bb)->p.Any:p.Any#[imm,?]():p.Dool;}
~-----------
~mut p.Any:{'this #[T:imm]:T}
~mut p.Box[X:imm,mut,read]:{'this .f[R:imm,mut,read](_:p.F[X,X,R]):R}
~mut p.Dool:{'this }
~mut p.F[A:imm,B:imm,C:imm]:{'this #(_:A, _:B):C}
~mut p.User:{'this mut .go1[R:imm,mut,read](b:p.Box[R]):p.Dool->b.f[imm,p.Dool](imm p._AUser[R:imm,mut,read]:p.F[imm R,imm R,p.Dool]{'_ #(aa:imm R, bb:imm R):p.Dool->p.Any#[imm,p.Dool]}); mut .go2(b:p.Box[p.User]):p.Dool->b.f[imm,p.Dool](imm p._BUser:p.F[p.User,p.User,p.Dool]{'_ #(aa:p.User, bb:p.User):p.Dool->p.Any#[imm,p.Dool]})}
""",List.of("""
Any:{#[T]:T}
Dool:{}
F[A,B,C]:{ #(A,B):C }
Box[X:*]:{ .f[R:*](x: F[X,X,R]): R }
User:{
  mut .go1[R:*](b: Box[R]): Dool -> b.f({aa,bb->Any#});
  mut .go2(b: Box[User]): Dool -> b.f({aa,bb->Any#});
}
"""));}//Then try again with b: mut Box[User]: the idea is that the inference should be tolerant of RCs when there is no other option 

@Test void boundHidingSimplified(){okI("""
p.Any:{'this #[T:imm]:T@p.Any;}
p.Box:{'this .f[R:imm,mut,read](p.F[p.User,R]):R@p.Box;}
p.Dool:{'this}
p.F[A:imm, C:imm]:{'this #(A):C@p.F;}
p.User:{'this mut .go(p.Box):p.Dool@p.User;(b)->b:?.f(p._AUser:$?{'_ ? [?](?):?@!;(aa)->p.Any:?#():?;}:?):?;}
p._AUser:p.F[p.User,p.Dool]{'_ #(p.User):p.Dool@p._AUser;(aa)->p.Any:p.Any#[imm,?]():p.Dool;}
~-----------
~mut p.Any:{'this #[T:imm]:T}
~mut p.Box:{'this .f[R:imm,mut,read](_:p.F[p.User,R]):R}
~mut p.Dool:{'this }
~mut p.F[A:imm,C:imm]:{'this #(_:A):C}
~mut p.User:{'this mut .go(b:p.Box):p.Dool->b.f[imm,p.Dool](imm p._AUser:p.F[p.User,p.Dool]{'_ #(aa:p.User):p.Dool->p.Any#[imm,p.Dool]})}
""",List.of("""
Any:{#[T]:T}
Dool:{}
F[A,C]:{ #(A):C }
Box:{ .f[R:*](x: F[User,R]): R }
User:{
  mut .go(b: Box): Dool -> b.f({aa->Any#});
}
"""));}

@Test void inferCallRC1(){okI("""
[###]
~-----------
~mut p.A:{'this\
 mut .foo123:p.A->this.foo123[mut];\
 read .foo123:p.A->this.foo123[read];\
 .bar:p.A->this.foo123[read]}
""",List.of("""
A:{mut .foo123:A->this.foo123; read .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}

@Test void inferCallRC2(){okI("""
[###]
~-----------
~mut p.A:{'this\
 mut .foo123:p.A->this.foo123[mut];\
 .bar:p.A->this.foo123[mut]}
""",List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}

@Test void inferCallRC3(){okI("""
[###]
~-----------
~mut p.A:{'this .foo123:p.A->this.foo123[imm]; read .foo123:p.A->this.foo123[read]; mut .bar:p.A->this.foo123[read]}
""",List.of("""
A:{imm .foo123:A->this.foo123; read .foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}

@Test void deepMethGenInference1(){okI("""
[###]~-----------
~mut p.A:{'this .f(aaaa:mut p.A):read p.B->read p.BB:p.B{'_\
 read .foo:p.B->p.Skip#[imm,read p.A](p.Id#[imm,read p.A](aaaa))}}
[###]
""",
//Somehow it now passes by accident; This needs to get some knowledge of capture to pass reliably
List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[read A](Id#(aaaa));}}
"""));}
@Test void deepMethGenInference2(){okI("""
[###]~-----------
~mut p.A:{'this .f(aaaa:mut p.A):read p.B->read p.BB:p.B{'_\
 read .foo:p.B->p.Skip#[imm,read p.A](p.Id#[imm,read p.A](aaaa))}}
[###]
""",List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#[read A](aaaa));}}
"""));}
@Test void deepMethGenInference3(){okI("""
[###]~-----------
~mut p.A:{'this .f(aaaa:mut p.A):read p.B->read p.BB:p.B{'_\
 read .foo:p.B->p.Skip#[imm,mut p.A](p.Id#[imm,mut p.A](aaaa))}}
[###]
""",List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
"""));}
@Test void regressionInfUnknown(){okI("""
[###]~-----------
~mut p.A:{'this }
~mut p.Get:{'this .get:iso p.A}
~mut p.User:{'this read .m(pppName:mut p.A):mut p.A->\
read p._BUser:p.Wrap{'_ read .wrap:p.Get->\
mut p._AUser:p.Get{'_ .get:iso p.A->pppName}}}
~mut p.Wrap:{'this read .wrap:p.Get}
""",List.of("""
A:{}
Get:{ imm .get: iso A; }
Wrap:{ read .wrap: imm Get; }
User:{
  read .m(pppName:mut A):mut A->
    read Wrap{ mut Get{ pppName } };
}
"""));}


@Test void regressionWasLooping(){okI("""
[###]~-----------
~mut p.A:{'this }
~mut p.B:{'this }
~mut p.Need:{'this #(a:mut p.A):p.B->p.B}
~mut p.User:{'this .f:p.B->p.Need#[imm](p.A)}
""",List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
A:{}
User:{
  .f:B->
    Need#(A{});
}
"""));}


@Test void challenge1(){okI("""
[###]
~mut p.User:{'this\
 .go(e:p.E1):p.E2->p.Map#[imm,p.E1,p.E2]\
(e, imm p._AUser:p.F[p.E1,p.E2]{'_ #(_:p.E1):p.E2->p.E2})}
""",List.of("""
F[R]:{#:R}
F[A,R]:{#(A):R}
F[A,B,R]:{#(A,B):R}
F[A,B,C,R]:{#(A,B,C):R}
E1:{}
E2:{}
Map:{#[A,R](a:A,f:F[A,R]):R->f#a }
User:{.go(e:E1):E2->Map#(e,{_->E2}) }
"""));}

@Test void challenge2(){okI("""
[###]
~mut p.User:{'this\
 .go(e:p.E1):p.E2->p.Map#[imm,p.E1,p.E2]\
(imm p._AUser:p.F[p.E1,p.E2]{'_ #(_:p.E1):p.E2->p.E2}, e)}
""",List.of("""
F[R]:{#:R}
F[A,R]:{#(A):R}
F[A,B,R]:{#(A,B):R}
F[A,B,C,R]:{#(A,B,C):R}
E1:{}
E2:{}
Map:{#[A,R](f:F[A,R],a:A):R->f#a }
User:{.go(e:E1):E2->Map#({_->E2},e) }
"""));}

@Test void challenge3(){okI("""
[###]
~mut p.Snd:{'this #[A:imm](x:p.Int):p.F[A,A]->imm p._ASnd[A:imm]:p.F[imm A,imm A]{'_ #(y:imm A):imm A->y}}
~mut p.User2:{'this .go2:p.Float->p.Snd#[imm,p.Float](p.Int)#[imm](p.Float)}
""",List.of("""
F[A,R]:{#(A):R}
Int:{}
Float:{}
Snd:{#[A](x:Int):F[A,A]->{y->y}}
User2:{.go2:Float->(Snd#Int)#Float}
"""));}

@Test void challengeRegressionLiteral(){okI("""
[###]
~mut p.TestIt:{'this .go:p.Float->p.Trash#[imm,p.Int](p.One)}
~mut p.Trash:{'this #[T:imm](_:T):p.Float->p.FOne}
""",List.of("""
Int:base.WidenTo[Int]{}
One:Int{}
Float:base.WidenTo[Float]{}
FOne:Float{}
Trash:{#[T](T):Float->FOne}
TestIt:{.go:Float->Trash#(One) }
"""));}


@Test void challenge4WithCorrectInferUnknown(){okI("""
[###]
~mut p.User3:{'this .go3:p.Float->p.Trash#[imm,p.F[base.InferUnknown,base.InferUnknown]](p.Top.top[imm,base.InferUnknown](imm p._BUser:p.F[p.Int,p.F[base.InferUnknown,base.InferUnknown]]{'_ #(x:p.Int):p.F[base.InferUnknown,base.InferUnknown]->imm p._AUser:p.F[base.InferUnknown,base.InferUnknown]{'_ #(y:base.InferUnknown):base.InferUnknown->y}})#[imm](p.One))}
~mut p.User4:{'this .dec[A:imm]:p.F[p.Int,p.F[A,A]]->imm p._DUser[A:imm]:p.F[p.Int,p.F[A,A]]{'_ #(x:p.Int):p.F[imm A,imm A]->imm p._CUser[A:imm]:p.F[imm A,imm A]{'_ #(y:imm A):imm A->y}}; .use:p.Int->this.dec[imm,p.Int]#[imm](p.One)#[imm](p.One)}
~mut p.User5:{'this .go3:p.Float->p.Trash#[imm,p.Float](p.Top.top[imm,p.Float](imm p._FUser:p.F[p.Int,p.F[p.Float,p.Float]]{'_ #(x:p.Int):p.F[p.Float,p.Float]->imm p._EUser:p.F[p.Float,p.Float]{'_ #(y:p.Float):p.Float->y}})#[imm](p.One)#[imm](p.FOne))}
""",List.of("""
F[A,R]:{#(A):R}
Int:base.WidenTo[Int]{}
One:Int{}
Float:base.WidenTo[Float]{}
FOne:Float{}
Snd:{#[A](x:Int):F[A,A]->{y->y}}
User1:{.go1[B]:F[B,B]->Snd#One}
User2:{.go2:Float->(Snd#One)#FOne}
Top:{.top[A](p:F[Int,F[A,A]]):F[Int,F[A,A]]->p}
Trash:{#[T](T):Float->FOne}
User3:{.go3:Float->Trash#(Top.top {x->{y->y}} # One) }
As[T]:{#(t:T):T->t}
User4:{
  .dec[A]:F[Int,F[A,A]]->{x->{y->y}};
  .use:Int-> this.dec # One # One
}
User5:{.go3:Float->Trash#(Top.top {x->{y->y}} # One # FOne) }
"""));}

//TODO: why the fresh names are different wrt the one before with User3???
@Test void challenge4CommentedCorrectInferUnknown(){okI("""
[###]
~mut p.User4:{'this .dec[A:imm]:p.F[p.Int,p.F[A,A]]->imm p._BUser[A:imm]:p.F[p.Int,p.F[A,A]]{'_ #(x:p.Int):p.F[imm A,imm A]->imm p._AUser[A:imm]:p.F[imm A,imm A]{'_ #(y:imm A):imm A->y}}; .use:p.Int->this.dec[imm,p.Int]#[imm](p.One)#[imm](p.One)}
~mut p.User5:{'this .go3:p.Float->p.Trash#[imm,p.Float](p.Top.top[imm,p.Float](imm p._DUser:p.F[p.Int,p.F[p.Float,p.Float]]{'_ #(x:p.Int):p.F[p.Float,p.Float]->imm p._CUser:p.F[p.Float,p.Float]{'_ #(y:p.Float):p.Float->y}})#[imm](p.One)#[imm](p.FOne))}""",List.of("""
F[A,R]:{#(A):R}
Int:base.WidenTo[Int]{}
One:Int{}
Float:base.WidenTo[Float]{}
FOne:Float{}
Snd:{#[A](x:Int):F[A,A]->{y->y}}
User1:{.go1[B]:F[B,B]->Snd#One}
User2:{.go2:Float->(Snd#One)#FOne}
Top:{.top[A](p:F[Int,F[A,A]]):F[Int,F[A,A]]->p}
Trash:{#[T](T):Float->FOne}
//User3:{.go3:Float->Trash#(Top.top {x->{y->y}} # One) }
As[T]:{#(t:T):T->t}
User4:{
  .dec[A]:F[Int,F[A,A]]->{x->{y->y}};
  .use:Int-> this.dec # One # One
}
User5:{.go3:Float->Trash#(Top.top {x->{y->y}} # One # FOne) }
"""));}

@Test void innerAbstract(){failI("""
In file: [###]/in_memory0.fear

003| Main:{
004|   .m:A -> { .bar:A }.foo
   |           ~~^^^^^^~~----
005|   }

While inspecting method declaration > object literal > method body > method declaration > type declaration body > type declaration > full file
Abstract method declaration for ".bar: A".
Only top level methods can be abstract.
Error 9 WellFormedness
""",List.of("""
A:{}
Main:{
  .m:A -> { .bar:A }.foo
  }
"""));}


@Test void captureThisX(){okI("""
[###]
~mut p.A[X:imm]:{'this .bar:p.Foo; .makeTrash:p.Foo->imm p._AA[X:imm]:p.Foo{'_ .capture:p.Foo->this.bar[imm]}}
~mut p.Foo:{'this .capture:p.Foo}
""",List.of("""
Foo:{.capture:Foo}
A[X]:{
  .bar:Foo; 
  .makeTrash:Foo->{.capture->this.bar}
  }
"""));}

@Test void captureThisXZ(){okI("""
[###]
~mut p.A[X:imm]:{'this .bar[K:imm]:p.Foo[K]; .makeTrash[Z:imm]:p.Foo[Z]->imm p._AA[Z:imm,X:imm]:p.Foo[imm Z]{'_ .capture:p.Foo[imm Z]->this.bar[imm,imm Z]}}
~mut p.Foo[Z:imm]:{'this .capture:p.Foo[Z]}
""",List.of("""
Foo[Z]:{.capture:Foo[Z]}
A[X]:{
  .bar[K]:Foo[K]; 
  .makeTrash[Z]:Foo[Z]->{.capture->this.bar}
  }
"""));}

@Test void captureNested(){okI("""
[###]
~mut p.OrderBy[T:imm]:p.F[T,read p.Order[T]]{'this .view[A:imm](f:p.F[A,read T]):p.OrderBy[A]->imm p._BOrde[A:imm,T:imm]:p.OrderBy[imm A], p.F[imm A,read p.Order[imm A]]{'_ #(a:imm A):read p.Order[imm A]->read p._AOrde[A:imm,T:imm]:p.Order[imm A]{'_ <=>(b:imm A):p.Void->this#[imm](f#[imm](a))<=>[imm](f#[imm](b))}; .view[_AA:imm](_:p.F[_AA,read A]):p.OrderBy[_AA]}; #(_:T):read p.Order[T]}
[###]
""",List.of("""
F[A,B]:{#(A):B}
Void:{}
Order[T]: { <=>(other: T): Void; }
OrderBy[T]:F[T,read Order[T]]{
  .view[A](f: F[A,read T]): OrderBy[A] ->
    {a-> {b-> this#(f#a) <=> (f#b) } };
  }
"""));}

@Test void partialTypeSig1(){okI("""
[###]
~mut p.Map:{'this .of[A:imm,B:imm,R:imm](a:A, f:p.GF[A,R]):p.F[B,R]->imm p._AMap[B:imm,R:imm,A:imm]:p.F[imm B,imm R]{'_ #(b:imm B):imm R->f.core[imm,imm B](a, b)}}
[###]
~mut p.User:{'this .done[Y:imm](t1:p.T1, t2:p.T2, y:Y):p.T3[Y]->p.Map.of[imm,p.T1,imm Y,p.T3[Y]](t1, imm p._AUser[Y:imm]:p.GF[p.T1,p.T3[Y]]{'_ .core[WW:imm](a:p.T1, b:WW):p.T3[imm WW]->a.and[imm,imm WW](b)})#[imm](y)}
""",List.of("""
GF[A,R]:{.core[B](A,B):R}
F[A,R]:{#(A):R}
T1:{.and[X](X):T3[X]}
T2:{}
T3[X]:{.x:X}
Map:{.of[A,B,R](a:A,f:GF[A,R]):F[B,R]->{b->f.core(a,b)}}
User:{.done[Y](t1:T1,t2:T2,y:Y):T3[Y]->
  Map.of(t1,{.core[WW](a,b)-> a.and(b)})#y }
"""));}

@Test void partialTypeSig1Sub(){okI("""
[###]
~mut p.Map:{'this .of[A:imm,B:imm,R:imm](a:A, f:p.GF[A,R]):p.F[B,R]->imm p._AMap[B:imm,R:imm,A:imm]:p.F[imm B,imm R]{'_ #(b:imm B):imm R->f.core[imm,imm B](a, b)}}
[###]
~mut p.User:{'this .done[Y:imm](t1:p.T1, t2:p.T2, y:Y):p.AnyT3->p.Map.of[imm,p.T1,imm Y,p.AnyT3](t1, imm p._AUser:p.GF[p.T1,p.AnyT3]{'_ .core[WW:imm](a:p.T1, b:WW):p.T3[imm WW]->a.and[imm,imm WW](b)})#[imm](y)}
""",List.of("""
GF[A,R]:{.core[B](A,B):R}
F[A,R]:{#(A):R}
T1:{.and[X](X):T3[X]}
T2:{}
T3[X]:AnyT3{.x:X}
AnyT3:{}
Map:{.of[A,B,R](a:A,f:GF[A,R]):F[B,R]->{b->f.core(a,b)}}
User:{.done[Y](t1:T1,t2:T2,y:Y):AnyT3->
  Map.of(t1,{.core[WW](a,b)-> a.and(b)})#y }
"""));}


@Test void partialTypeSigImplicit1(){okI("""
[###]
~mut p.Map:{'this .of[A:imm,B:imm,R:imm](a:A, f:p.GF[A,R]):p.F[B,R]->imm p._AMap[B:imm,R:imm,A:imm]:p.F[imm B,imm R]{'_ #(b:imm B):imm R->f.core[imm,imm B](a, b)}}
[###]
~mut p.User:{'this .done[Y:imm](t1:p.T1, t2:p.T2, y:Y):p.T3[Y]->p.Map.of[imm,p.T1,imm Y,p.T3[Y]](t1, imm p._AUser[Y:imm]:p.GF[p.T1,p.T3[Y]]{'_ .core[B:imm](a:p.T1, b:B):p.T3[imm B]->a.and[imm,imm B](b)})#[imm](y)}
""",List.of("""
GF[A,R]:{.core[B](A,B):R}
F[A,R]:{#(A):R}
T1:{.and[X](X):T3[X]}
T2:{}
T3[X]:{.x:X}
Map:{.of[A,B,R](a:A,f:GF[A,R]):F[B,R]->{b->f.core(a,b)}}
User:{.done[Y](t1:T1,t2:T2,y:Y):T3[Y]->
  Map.of(t1,{.core(a,b)-> a.and(b)})#y }
"""));}

@Test void wrongTargsTooManyDoesNotLeakClsBinder1(){okI("""
[###]
~mut p.User:{'this .go:p.Bool->p.Flows.flow[read].mapping[imm,p.KeyElem[p.Str,p.Info],p.Str,p.Info](imm p._AUser:p.KeyElemMapper[p.KeyElem[p.Str,p.Info],p.Str,p.Info]{'_ .key(e:p.KeyElem[p.Str,p.Info]):p.Str->e.key[imm]; .elem(e:p.KeyElem[p.Str,p.Info]):p.Info->e.elem[imm]})}
""",List.of("""
Str:{} Info:{} Bool:{} True:{} False:{}
KeyElem[K,E]:{.key:K;.elem:E;}
KeyElemMapper[A,K,E]:{.key(A):K;.elem(A):E;}

Flow[TTT]:{
  .mapping[K,E](m:KeyElemMapper[TTT,Str,Info]):Bool;
}

Flows:{
  read .flow:Flow[KeyElem[Str,Info]]->{
    .mapping[K,E](m:KeyElemMapper[KeyElem[Str,Info],Str,Info]):Bool->True;
  };
}

User:{.go:Bool->
  // WRONG: mapping has 2 method binders [K,E], but we pass 3 targs (old bug path).
  Flows.flow.mapping[KeyElem[Str,Info],Str,Info]({
    .key(e)->e.key;
    .elem(e)->e.elem;
  });
}
"""));}

@Test void wrongTargsTooFewPadsErr1(){okI("""
[###]
~mut p.User:{'this .go:p.Bool->p.Flows.flow[read].mapping[imm,p.Str](imm p._AUser:p.KeyElemMapper[p.KeyElem[p.Str,p.Info],p.Str,p.Info]{'_ .key(e:p.KeyElem[p.Str,p.Info]):p.Str->e.key[imm]; .elem(e:p.KeyElem[p.Str,p.Info]):p.Info->e.elem[imm]})}
""",List.of("""
Str:{} Info:{} Bool:{} True:{} False:{}
KeyElem[K,E]:{.key:K;.elem:E;}
KeyElemMapper[A,K,E]:{.key(A):K;.elem(A):E;}

Flow[TTT]:{
  .mapping[K,E](m:KeyElemMapper[TTT,Str,Info]):Bool;
}

Flows:{
  read .flow:Flow[KeyElem[Str,Info]]->{
    .mapping[K,E](m:KeyElemMapper[KeyElem[Str,Info],Str,Info]):Bool->True;
  };
}

User:{.go:Bool->
  // WRONG: only 1 targ, should be 2. Missing one should be padded with IT.Err during inference.
  Flows.flow.mapping[Str]({
    .key(e)->e.key;
    .elem(e)->e.elem;
  });
}
"""));}

@Test void wrongTargsTooManyWithUsedBinders2(){okI("""
[###]
~mut p.Flows:{'this read .flow:p.Flow[p.KeyElem[p.Str,p.Info]]->imm p._AFlow:p.Flow[p.KeyElem[p.Str,p.Info]]{'_ .mapping[K:imm,E:imm](m:p.KeyElemMapper[p.KeyElem[p.Str,p.Info],K,E]):p.Bool->p.True}}
~mut p.Info:{'this }
~mut p.KeyElemMapper[A:imm,K:imm,E:imm]:{'this .key(_:A):K; .elem(_:A):E}
~mut p.KeyElem[K:imm,E:imm]:{'this .key:K; .elem:E}
~mut p.Str:{'this }
~mut p.True:{'this }
~mut p.User:{'this .go:p.Bool->p.Flows.flow[read].mapping[imm,p.KeyElem[p.Str,p.Info],p.Str,p.Info](imm p._AUser:p.KeyElemMapper[p.KeyElem[p.Str,p.Info],p.Str,p.Info]{'_ .key(e:p.KeyElem[p.Str,p.Info]):p.Str->e.key[imm]; .elem(e:p.KeyElem[p.Str,p.Info]):p.Info->e.elem[imm]})}
""",List.of("""
Str:{} Info:{} Bool:{} True:{} False:{}
KeyElem[K,E]:{.key:K;.elem:E;}
KeyElemMapper[A,K,E]:{.key(A):K;.elem(A):E;}

Flow[TTT]:{
  // Here K/E are USED in the parameter type, so trimming/padding really affects inference.
  .mapping[K,E](m:KeyElemMapper[TTT,K,E]):Bool;
}

Flows:{
  read .flow:Flow[KeyElem[Str,Info]]->{
    .mapping[K,E](m:KeyElemMapper[KeyElem[Str,Info],K,E]):Bool->True;
  };
}

User:{.go:Bool->
  // WRONG: 3 targs given to a 2-binder method. Old code would keep KeyElemMapper[TTT,K,E] raw and leak TTT.
  Flows.flow.mapping[KeyElem[Str,Info],Str,Info]({
    .key(e)->e.key;
    .elem(e)->e.elem;
  });
}
"""));} 

@Test void toStr(){okI("""
[###]
~mut p.Top:{'this .m(b:p.Box[p.A]):p.Str->\
b.str[read](imm p._ATop:p.ToStrBy[p.A]{'_\
 #(_aimpl:read p.A):read p.ToStr->_aimpl})}
""",List.of("""
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }
Box[EE:*]: ToStr[EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .str by-> by#(this.get).str
  }
A:ToStr{ .str->Str}
Top:{ 
  .m(b:Box[A]):Str -> b.str {::} 
  }
"""));}
@Test void inferFromExpected_swap_ok(){ okI("""
[###]
~mut p.Use:{'this read .u:p.Bar[p.Nat,p.Str]->p.Mk.mk[read,p.Str,p.Nat]}
""",List.of("""
Nat:{} Str:{}
Bar[X:*,Y:*]:{}
Foo[A:*,B:*]:Bar[B,A]{}

Mk:{ read .mk[A:*,B:*]: Foo[A,B] -> this.mk; }
Use:{
  // Must infer A=Str, B=Nat from expected Bar[Nat,Str] via Foo[A,B]:Bar[B,A]
  read .u: Bar[Nat,Str] -> Mk.mk;
}
""")); }

@Test void inferFromExpected_nested_ok(){ okI("""
[###]
~mut p.Use:{'this read .u:p.Bar[p.Nat,p.List[p.Str]]->p.Mk.mk[read,p.Str,p.Nat]}
""",List.of("""
Nat:{} Str:{} List[T:*]:{}
Bar[X:*,Y:*]:{}
Foo[A:*,B:*]:Bar[B,List[A]]{}

Mk:{ read .mk[A:*,B:*]: Foo[A,B] -> this.mk; }

Use:{
  // Must infer A=Str, B=Nat from expected Bar[Nat,List[Str]]
  read .u: Bar[Nat,List[Str]] -> Mk.mk;
}
""")); }

@Test void inferFromExpected_recursive_ok(){ okI("""
[###]
~mut p.Use:{'this read .u:p.Bar3[p.Nat,p.Str,p.Foo[p.Str,p.Nat]]->p.Mk.mk[read,p.Str,p.Nat]}
""",List.of("""
Nat:{} Str:{}
Bar3[X:*,Y:*,Z:*]:{}
Foo[A:*,B:*]:Bar3[B,A,Foo[A,B]]{}

Mk:{ read .mk[A:*,B:*]: Foo[A,B] -> this.mk; }

Use:{
  // Must infer A=Str, B=Nat and also match the recursive slot Foo[Str,Nat]
  read .u: Bar3[Nat,Str,Foo[Str,Nat]] -> Mk.mk;
}
""")); }

@Test void inferFromExpected_multiHop_ok(){ okI("""
[###]
~mut p.Use:{'this read .u:p.Bar[p.Nat,p.Str]->p.Mk.mk[read,p.Str,p.Nat]}
""",List.of("""
Nat:{} Str:{}
Bar[X:*,Y:*]:{}
Mid[A:*,B:*]:Bar[B,A]{}
Foo[A:*,B:*]:Mid[A,B]{}

Mk:{ read .mk[A:*,B:*]: Foo[A,B] -> this.mk; }

Use:{
  // Must still infer through Foo -> Mid -> Bar (tests transitive super walking)
  read .u: Bar[Nat,Str] -> Mk.mk;
}
""")); }

@Test void inferFromExpected_partial_ok(){ okI("""
[###]
~mut p.Use:{'this read .u:p.Bar1[p.Nat]->p.Mk.mk[read,base.InferUnknown,p.Nat]}
""",List.of("""
Nat:{} Str:{}
Bar1[X:*]:{}
Foo[A:*,B:*]:Bar1[B]{}

Mk:{ read .mk[A:*,B:*]: Foo[A,B] -> this.mk; }

Use:{
  // Only constrains B=Nat; A is unconstrained. Should still compile.
  read .u: Bar1[Nat] -> Mk.mk;
}
""")); }

@Test void inferInInheritedSigMethLocal(){ okI("""
[###]
~mut p.User1:{'this .foo:p.B->imm p.C1:p.B{'_\
 .m(a:p.A):p.A->a.baz[imm]}}
~mut p.User2:{'this .foo:p.B->imm p._AUser:p.B{'_\
 .m(a:p.A):p.A->p.Any![imm,p.A]}}
~mut p.User3:{'this .foo:p.B->imm p.C3:p.B{'_\
 .m(a:p.A):p.A->p.Any![imm,p.A]}}
""",List.of("""
Any:{![T]:T->Any!}
A:{.baz:A}
B:{ .m(a:A):A; }
User1:{ .foo:B->C1:B{ .m a->a.baz; }}
User2:{ .foo:B->B{ .m a->Any!; }}
User3:{ .foo:B->C3:B{ .m a->Any!; }}
""")); }

@Test void miniBox(){okI("""
p.Box[EE:imm,mut,read]:{'this .get:imm EE@p.Box;}
p.Boxs1:{'this #[ET:imm,mut,read](ET):mut p.Box[ET]@p.Boxs1;(e)->p._ABoxs:$?{'_ .get[?]:?@!;->e:?;}:?;}
p._ABoxs[ET:imm,mut,read]:p.Box[ET]{'_ .get:imm ET@p._ABoxs;->e:imm ET;}
~-----------
~mut p.Box[EE:imm,mut,read]:{'this .get:imm EE}
~mut p.Boxs1:{'this #[ET:imm,mut,read](e:ET):mut p.Box[ET]->mut p._ABoxs[ET:imm,mut,read]:p.Box[ET]{'_ .get:imm ET->e}}
""",List.of("""
Box[EE:*]:{
  imm  .get: imm EE;
  }
Boxs1:{#[ET:*](e:ET):mut Box[ET]->{ imm .get ->e } }
"""));}

@Test void simpleBox(){okI("""
p.Box[EE:imm,mut,read]:{'this mut .get:EE@p.Box; read .get:read/imm EE@p.Box; .get:imm EE@p.Box;}
p.Boxs1:{'this #[ET:imm,mut,read](ET):mut p.Box[ET]@p.Boxs1;(e)->p._ABoxs:$?{'_ mut .get[?]:?@!;->e:?; read .get[?]:?@!;->e:?; .get[?]:?@!;->e:?;}:?;}
p.Boxs:{'this #[ET:imm,mut,read](ET):mut p.Box[ET]@p.Boxs;(e)->p._BBoxs:$?{'_ ? [?]:?@!;->e:?;}:?;}
p._ABoxs[ET:imm,mut,read]:p.Box[ET]{'_ mut .get:ET@p._ABoxs;->e:ET; read .get:read/imm ET@p._ABoxs;->e:ET; .get:imm ET@p._ABoxs;->e:imm ET;}
p._BBoxs[ET:imm,mut,read]:p.Box[ET]{'_ mut .get:ET@p._BBoxs;->e:ET; read .get:read/imm ET@p._BBoxs;->e:ET; .get:imm ET@p._BBoxs;->e:imm ET;}
~-----------
~mut p.Box[EE:imm,mut,read]:{'this mut .get:EE; read .get:read/imm EE; .get:imm EE}
~mut p.Boxs1:{'this #[ET:imm,mut,read](e:ET):mut p.Box[ET]->mut p._ABoxs[ET:imm,mut,read]:p.Box[ET]{'_ mut .get:ET->e; read .get:read/imm ET->e; .get:imm ET->e}}
~mut p.Boxs:{'this #[ET:imm,mut,read](e:ET):mut p.Box[ET]->mut p._BBoxs[ET:imm,mut,read]:p.Box[ET]{'_ mut .get:ET->e; read .get:read/imm ET->e; .get:imm ET->e}}
""",List.of("""
Box[EE:*]:{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  }
Boxs1:{#[ET:*](e:ET):mut Box[ET]->{
  mut .get ->e;
  read .get ->e;
  imm .get ->e;
  }}
Boxs:{#[ET:*](e:ET):mut Box[ET]->{e}}
"""));}
}