package inference;

import java.util.List;

import org.junit.jupiter.api.Test;

public class TestInferenceSteps {
  static void okI(String expected, List<String> input){ TestInference.ok(expected,"role app000;",input,true); }
  static void okI(String expected, String head, List<String> input){ TestInference.ok(expected,head,input,true); }
  static void failI(String expected, List<String> input){ TestInference.fail(expected,"role app000;",input,true); }
  static void failI(String expected, String head, List<String> input){ TestInference.fail(expected,head,input,true); }  
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
~mut p.A:{'this .foo[X:imm](x:X):X->this.foo[imm,X](x)}
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
p._CStac[T:imm]:base.ThenElse[p.Stack[T]]{'_ mut .then:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T]+[imm](e:T):p.Stack[T]; mut .else:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T];}
p._DStac[T:imm]:p.Stack[T]{'_ .match[_GR:imm](p.StackMatch[T,_GR]):_GR@p._DStac;(m)->m:p.StackMatch[T,_GR].elem[imm](e:T,this:p.Stack[T]):_GR; .fold[_HR:imm](_HR,base.F[_HR,T,_HR]):_HR@p._DStac;(start, f)->f:base.F[_HR,T,_HR]#[read](this:p.Stack[T].fold[imm,_HR](start:_HR,f:base.F[_HR,T,_HR]):_HR,e:T):_HR; .map[_JR:imm](base.F[T,_JR]):p.Stack[_JR]@p._DStac;(f)->this:p.Stack[T].map[imm,_JR](f:base.F[T,_JR]):p.Stack[_JR]+[imm](f:base.F[T,_JR]#[read](e:T):_JR):p.Stack[_JR]; .filter(base.F[T,base.Bool]):p.Stack[T]@p._DStac;(f)->f:base.F[T,base.Bool]#[read](e:T):base.Bool.if[imm,p.Stack[T]](mut p._CStac[T:imm]:base.ThenElse[p.Stack[T]]{'_ mut .then:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T]+[imm](e:T):p.Stack[T]; mut .else:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T];}:mut base.ThenElse[p.Stack[T]]):p.Stack[T]; +(T):p.Stack[T]@p.Stack;}
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
p.StackMatch[T:imm, R:imm]:{'this\
 .empty:R@p.StackMatch; .elem(T,p.Stack[T]):R@p.StackMatch;}
p.Stack[T:imm]:{'this\
 .match[R:imm](p.StackMatch[T,R]):R@p.Stack;(m)->m:?.empty():?;\
 .fold[R:imm](R,base.F[R,T,R]):R@p.Stack;(start, f)->start:?;\
 .map[R:imm](base.F[T,R]):p.Stack[R]@p.Stack;(f)->p._AStac:$?:?;\
 .filter(base.F[T,base.Bool]):p.Stack[T]@p.Stack;(f)->p._BStac:$?:?;\
 +(T):p.Stack[T]@p.Stack;(e)->p._DStac:$?{'_ ?\
 .match[?](?):?@!;(m)->m:?.elem(e:?,this:?):?;\
 ? .fold[?](?,?):?@!;(start, f)->f:?#(this:?.fold(start:?,f:?):?,e:?):?; ?\
 .map[?](?):?@!;(f)->this:?.map(f:?):?+(f:?#(e:?):?):?; ?\
 .filter[?](?):?@!;(f)->f:?#(e:?):?.if(p._CStac:$?{'_ ?\
 .then[?]:?@!;->this:?.filter(f:?):?+(e:?):?; ?\
 .else[?]:?@!;->this:?.filter(f:?):?;}:?):?;}:?;}
p._CStac[T:imm]:base.ThenElse[p.Stack[T]]{'_\
 mut .then:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](\
f:base.F[T,base.Bool]):p.Stack[T]+[imm](e:T):p.Stack[T];\
 mut .else:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](\
f:base.F[T,base.Bool]):p.Stack[T];}
p._DStac[T:imm]:p.Stack[T]{'_\
 .match[_GR:imm](p.StackMatch[T,_GR]):_GR@p._DStac;\
(m)->m:p.StackMatch[T,_GR].elem[imm](e:T,this:p.Stack[T]):_GR;\
 .fold[_HR:imm](_HR,base.F[_HR,T,_HR]):_HR@p._DStac;\
(start, f)->f:base.F[_HR,T,_HR]#[read](\
this:p.Stack[T].fold[imm,_HR](\
start:_HR,f:base.F[_HR,T,_HR]):_HR,e:T):_HR;\
 .map[_JR:imm](base.F[T,_JR]):p.Stack[_JR]@p._DStac;\
(f)->this:p.Stack[T].map[imm,_JR](f:base.F[T,_JR]):p.Stack[_JR]\
+[imm](f:base.F[T,_JR]#[read](e:T):_JR):p.Stack[_JR];\
 .filter(base.F[T,base.Bool]):p.Stack[T]@p._DStac;\
(f)->f:base.F[T,base.Bool]#[read](e:T):base.Bool.if[imm,p.Stack[T]](\
mut p._CStac[T:imm]:base.ThenElse[p.Stack[T]]{'_\
 mut .then:p.Stack[T]@p._CStac;\
->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T]\
+[imm](e:T):p.Stack[T];\
 mut .else:p.Stack[T]@p._CStac;->this:p.Stack[T].filter[imm](\
f:base.F[T,base.Bool]):p.Stack[T];}:mut base.ThenElse[p.Stack[T]]):p.Stack[T];\
 +(T):p.Stack[T]@p.Stack;}
~-----------
~mut p.StackMatch[T:imm,R:imm]:{'this\
 .empty:R; .elem(_:T, _:p.Stack[T]):R}
~mut p.Stack[T:imm]:{'this\
 .match[R:imm](m:p.StackMatch[T,R]):R->m.empty[imm];\
 .fold[R:imm](start:R, f:base.F[R,T,R]):R->start;\
 .map[R:imm](f:base.F[T,R]):p.Stack[R]->p.Stack[R];\
 .filter(f:base.F[T,base.Bool]):p.Stack[T]->p.Stack[T];\
 +(e:T):p.Stack[T]->imm p._DStac[T:imm]:p.Stack[T]{'_\
 .match[_GR:imm](m:p.StackMatch[T,_GR]):_GR->m.elem[imm](e, this);\
 .fold[_HR:imm](start:_HR, f:base.F[_HR,T,_HR]):_HR->f#[read](\
this.fold[imm,_HR](start, f), e);\
 .map[_JR:imm](f:base.F[T,_JR]):p.Stack[_JR]->\
this.map[imm,_JR](f)+[imm](f#[read](e));\
 .filter(f:base.F[T,base.Bool]):p.Stack[T]->\
f#[read](e).if[imm,p.Stack[T]](mut p._CStac[T:imm]:base.ThenElse[p.Stack[T]]{'_\
 mut .then:p.Stack[T]->this.filter[imm](f)+[imm](e);\
 mut .else:p.Stack[T]->this.filter[imm](f)});\
 +(_:T):p.Stack[T]}}
""",importTo10,List.of(stackStart));}
//Note: the last +(_:T):p.Stack[T] is correct, the (not printed) source would point to the origin of the method and impl 

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
p._AUser:p.GG[C,D]{'_ .apply[_AC:imm,_AD:imm](_AC,_AD,_AC):_AD@p._AUser;(a, b, c)->p.Any:p.Any![imm,?]():_AD;}
p._BUser:p.GG[C,D]{'_ .apply[_BC:imm,_BD:imm](_BC,_BD,_BC):_BD@p._BUser;(a, b, c)->p.Any:p.Any![imm,?]():_BD;}
~-----------
~mut p.Any:{'this ![T:imm]:T->p.Any![imm,T]}
~mut p.Baba[C:imm,D:imm]:p.GG[p.Any,p.Any]{'this .apply[_AC:imm,_AD:imm](_:p.Any, _:p.Any, _:_AC):_AD}
~mut p.GG[A:imm,B:imm]:{'this .apply[C:imm,D:imm](_:A, _:B, _:C):D}
~mut p.User:{'this .withGG[A1:imm,B1:imm](_:p.GG[A1,B1]):p.User; .foo1[C:imm,D:imm]:p.User->this.withGG[imm,C,D](imm p._AUser:p.GG[C,D]{'_ .apply[_AC:imm,_AD:imm](a:_AC, b:_AD, c:_AC):_AD->p.Any![imm,_AD]}); .foo2[C:imm,D:imm]:p.User->imm p.KK:{'_ .k[K:imm]:K->this.withGG[imm,C,D](imm p._BUser:p.GG[C,D]{'_ .apply[_BC:imm,_BD:imm](a:_BC, b:_BD, c:_BC):_BD->p.Any![imm,_BD]})}.k[imm,p.User]}
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
~mut p.User:{'this .m:p.User->imm p._AUser:{'_ .bla:p.User->p.User}.bla[imm]}
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
   |                ^^^^^^^^^^

While inspecting literal implementing type "p.A"
Cannot infer return type of method ".m:?".
No supertype has a method named ".m" with 0 parameters.
Error 9 WellFormedness
""",List.of("""
A:{}
User:{ .m:A->{ .m->A;}; }
"""));}

@Test void badSealedOutNoInference(){failI("""
In file: [###]/in_memory0.fear

003| User:base.Void{ .m:A->A }
   | ^^^^^

While inspecting type declaration "User"
Type "User" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",List.of("""
A:{}
User:base.Void{ .m:A->A }
"""));}

//Controversial, but I think it should fail
@Test void badSealedOutEmpty(){failI("""
In file: [###]/in_memory0.fear

003| User:base.Void{}
   | ^^^^^

While inspecting type declaration "User"
Type "User" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",List.of("""
A:{}
User:base.Void{}
"""));}

@Test void badSealedOutInferenceUsed(){failI("""
In file: [###]/in_memory0.fear

003| User:Void{ .m:A->A }
   | ^^^^^

While inspecting type declaration "User"
Type "User" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Type "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9 WellFormedness
""",importMini,List.of("""
A:{}
User:Void{ .m:A->A }
"""));}

@Test void badSealedOutInferenceInner(){failI("""
In file: [###]/in_memory0.fear

003| User:{ .m:base.Void->{ .m:A->A;}; }
   | ^^^^^^

While inspecting literal implementing type "base.Void"
Literal implementing type "base.Void" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Literal implementing type "base.Void" is defined in package "p".
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
p.C:p.A, p.B{'this .m:base.Nat@p.B;}
~-----------
~mut p.A:{'this .m:base.Nat->base.1}
~mut p.B:p.A{'this .m:base.Nat->base.2}
~mut p.C:p.A, p.B{'this .m:base.Nat}
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
p._AMake[T:imm,mut,read]:p.Box[T]{'_ mut .expose:T@p._AMake;->t:T; read .get:read/imm T@p._AMake;->t:Err;}
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
p._AMake[T:imm,mut,read]:p.Box[T]{'_ mut .expose:T@p._AMake;->t:T; read .get:read/imm T@p._AMake;->t:Err;}
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

//TODO: if some error about rc disagreement cannot be triggered any more, they should become asserts
//search for 'Reference capability disagreement'


//Ok with inferErr here
@Test void recoverUserTypes1(){okI("""
[###]~-----------
~mut p.A:p.I{'this }
~mut p.B:p.I{'this }
~mut p.Foo:{'this .get[T:imm](a:T, b:T):T->a}
~mut p.I:{'this }
~mut p.User:{'this .m:p.I->p.Foo.get[imm,base.InferErr](p.A, p.B)}
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

}