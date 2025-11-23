package inferenceGrammar;

import java.util.List;

import org.junit.jupiter.api.Test;

public class TestInferenceSteps {
  static void okI(String expected, List<String> input){ TestInference.ok(expected,"role app000;",input,true); }
  static void okI(String expected, String head, List<String> input){ TestInference.ok(expected,head,input,true); }
  static void failI(String expected, List<String> input){ TestInference.fail(expected,"role app000;",input,true); }
  static void failI(String expected, String head, List<String> input){ TestInference.fail(expected,head,input,true); }  
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
p.A_User:p.F[p.User,p.User]{'_ imm #(p.User):p.User@p.A_User;\
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
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
p.Z0ExampleSum:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z0ExampleSum;\
(ns)->ns:p.Stack[base.Nat].fold[imm,base.Nat](\
base.0:base.Nat,p.A_Z0Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@p.A_Z0Ex;\
 (n1, n2)->n1:base.Nat+[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
""",importMini,List.of(stackStart+"""
Z0ExampleSum: { #(ns: Stack[Nat]): Nat -> ns.fold(0, { n1,n2 -> n1 + n2 })  }
"""));}
@Test void inferStackGuideExampleTimesLit(){okI("""
p.Z1ExampleTimes:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z1ExampleTimes;\
(ns)->ns:p.Stack[base.Nat]\
.fold[imm,base.Nat](\
base.1:base.Nat,\
p.A_Z1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@p.A_Z1Ex;\
 (n1, n2)->n1:base.Nat*[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
""",importMini,List.of(stackStart+"""
Z1ExampleTimes: { #(ns: Stack[Nat]): Nat -> ns.fold(1, { n1,n2 -> n1 * n2 })  }
"""));}

@Test void inferStackGuideExampleSumMatchLit(){okI("""
p.Z2Example:{'this\
 .sum(p.Stack[base.Nat]):base.Nat@p.Z2Example;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,base.Nat](\
p.A_Z2Ex:p.StackMatch[base.Nat,base.Nat]{'_\
 imm .empty:base.Nat@p.A_Z2Ex;\
 .empty()->base.0:base.Nat;\
 imm .elem(base.Nat,p.Stack[base.Nat]):base.Nat@p.A_Z2Ex;\
 .elem(top, tail)->top:base.Nat\
+[imm](this:p.Z2Example.sum[imm](tail:p.Stack[base.Nat]):base.Nat):base.Nat;\
}:p.StackMatch[base.Nat,base.Nat]):base.Nat;}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
""",importMini,List.of(stackStart+"""
Z2Example: {
  .sum(ns: Stack[Nat]): Nat -> ns.match{
    .empty -> 0;
    .elem(top, tail) -> top + ( this.sum(tail) );
    }
  }
"""));}

@Test void inferStackGuideExampleAdd5Lit(){okI("""
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
p.Z3ExampleAdd5:{'this\
 .add5(p.Stack[base.Nat]):p.Stack[base.Nat]@p.Z3ExampleAdd5;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,p.Stack[base.Nat]](\
p.B_Z3Ex:p.StackMatch[base.Nat,p.Stack[base.Nat]]{'_\
 imm .empty:p.Stack[base.Nat]@p.B_Z3Ex;\
 .empty()->p.Stack[base.Nat]:p.Stack[base.Nat];\
 imm .elem(base.Nat,p.Stack[base.Nat]):p.Stack[base.Nat]@p.B_Z3Ex;\
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
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
p.Z4ExampleFluent:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z4ExampleFluent;\
(ns)->ns:p.Stack[base.Nat].map[imm,base.Nat](\
p.A_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@p.A_Z4Ex;\
 (n)->n:base.Nat+[imm](base.10:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat]\
.map[imm,base.Nat](\
p.B_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@p.B_Z4Ex;\
 (n)->n:base.Nat*[imm](base.3:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat].fold[imm,base.Nat](\
base.0:base.Nat,p.C_Z4Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@p.C_Z4Ex;\
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
p.StackMatch[T:imm, R:imm]:{'this\
 .empty:R@p.StackMatch;\
 .elem(T,p.Stack[T]):R@p.StackMatch;}
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
 imm .match[G_R:imm](p.StackMatch[T,G_R]):G_R@p.D_Stac;\
 .match(m)->m:p.StackMatch[T,G_R].elem[imm](e:T,this:p.Stack[T]):G_R;\
 imm .fold[H_R:imm](H_R,base.F[H_R,T,H_R]):H_R@p.D_Stac;\
 .fold(start, f)->f:base.F[H_R,T,H_R]#[read](this:p.Stack[T].fold[imm,H_R](start:H_R,f:base.F[H_R,T,H_R]):H_R,e:T):H_R;\
 imm .map[J_R:imm](base.F[T,J_R]):p.Stack[J_R]@p.D_Stac;\
 .map(f)->this:p.Stack[T].map[imm,J_R](f:base.F[T,J_R]):p.Stack[J_R]\
+[imm](f:base.F[T,J_R]#[read](e:T):J_R):p.Stack[J_R];\
 imm .filter(base.F[T,base.Bool]):p.Stack[T]@p.D_Stac;\
 .filter(f)->f:base.F[T,base.Bool]#[read](e:T):base.Bool\
.if[imm,p.Stack[T]](mut p.C_Stac:base.ThenElse[p.Stack[T]]{'_\
 mut .then:p.Stack[T]@p.C_Stac;\
 .then()->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T]\
+[imm](e:T):p.Stack[T];\
 mut .else:p.Stack[T]@p.C_Stac;\
 .else()->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T];\
}:mut base.ThenElse[p.Stack[T]]):p.Stack[T];\
 imm +(T):p.Stack[T]@p.Stack;}:p.Stack[T];}
""",importTo10,List.of(stackStart));}

@Test void inferStackGuideExampleSum(){okI("""
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
p.Z0ExampleSum:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z0ExampleSum;\
(ns)->ns:p.Stack[base.Nat].fold[imm,base.Nat](\
base.Zero:base.Nat,p.A_Z0Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@p.A_Z0Ex;\
 (n1, n2)->n1:base.Nat+[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
""",importTo10,List.of(stackStart+"""
Z0ExampleSum: { #(ns: Stack[Nat]): Nat -> ns.fold(Zero, { n1,n2 -> n1 + n2 })  }
"""));}
@Test void inferStackGuideExampleTimes(){okI("""
p.Z1ExampleTimes:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z1ExampleTimes;\
(ns)->ns:p.Stack[base.Nat]\
.fold[imm,base.Nat](\
base.One:base.Nat,\
p.A_Z1Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@p.A_Z1Ex;\
 (n1, n2)->n1:base.Nat*[imm](n2:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat,base.Nat]):base.Nat;}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
""",importTo10,List.of(stackStart+"""
Z1ExampleTimes: { #(ns: Stack[Nat]): Nat -> ns.fold(One, { n1,n2 -> n1 * n2 })  }
"""));}

@Test void inferStackGuideExampleSumMatch(){okI("""
p.Z2Example:{'this\
 .sum(p.Stack[base.Nat]):base.Nat@p.Z2Example;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,base.Nat](\
p.A_Z2Ex:p.StackMatch[base.Nat,base.Nat]{'_\
 imm .empty:base.Nat@p.A_Z2Ex;\
 .empty()->base.Zero:base.Nat;\
 imm .elem(base.Nat,p.Stack[base.Nat]):base.Nat@p.A_Z2Ex;\
 .elem(top, tail)->top:base.Nat\
+[imm](this:p.Z2Example.sum[imm](tail:p.Stack[base.Nat]):base.Nat):base.Nat;\
}:p.StackMatch[base.Nat,base.Nat]):base.Nat;}
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
""",importTo10,List.of(stackStart+"""
Z2Example: {
  .sum(ns: Stack[Nat]): Nat -> ns.match{
    .empty -> Zero;
    .elem(top, tail) -> top + ( this.sum(tail) );
    }
  }
"""));}

@Test void inferStackGuideExampleAdd5(){okI("""
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
p.Z3ExampleAdd5:{'this\
 .add5(p.Stack[base.Nat]):p.Stack[base.Nat]@p.Z3ExampleAdd5;\
(ns)->ns:p.Stack[base.Nat]\
.match[imm,p.Stack[base.Nat]](\
p.B_Z3Ex:p.StackMatch[base.Nat,p.Stack[base.Nat]]{'_\
 imm .empty:p.Stack[base.Nat]@p.B_Z3Ex;\
 .empty()->p.Stack[base.Nat]:p.Stack[base.Nat];\
 imm .elem(base.Nat,p.Stack[base.Nat]):p.Stack[base.Nat]@p.B_Z3Ex;\
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
p.StackMatch[T:imm, R:imm]:{[###]}
p.Stack[T:imm]:{[###]}
p.Z4ExampleFluent:{'this\
 #(p.Stack[base.Nat]):base.Nat@p.Z4ExampleFluent;\
(ns)->ns:p.Stack[base.Nat].map[imm,base.Nat](\
p.A_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@p.A_Z4Ex;\
 (n)->n:base.Nat+[imm](base.Ten:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat]\
.map[imm,base.Nat](\
p.B_Z4Ex:base.F[base.Nat,base.Nat]{'_\
 read #(base.Nat):base.Nat@p.B_Z4Ex;\
 (n)->n:base.Nat*[imm](base.Three:base.Nat):base.Nat;\
}:base.F[base.Nat,base.Nat]):p.Stack[base.Nat].fold[imm,base.Nat](\
base.Zero:base.Nat,p.C_Z4Ex:base.F[base.Nat,base.Nat,base.Nat]{'_\
 read #(base.Nat,base.Nat):base.Nat@p.C_Z4Ex;\
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

@Test void boundChangesName(){okI("""
p.Foo[K:imm]:{'this\
 .get:K@p.Foo;\
 .beer[G:imm]:G@p.Foo;}
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1:p.A{'this\
 .m[Y:imm](p.Foo[Y]):Y@p.B1;\
(z)->z:p.Foo[Y].get[imm]():Y;}
p.B2:p.A{'this\
 .m[Y:imm](p.Foo[Y]):Y@p.B2;\
(z)->z:p.Foo[Y].beer[imm,Y]():Y;}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1:A{.m[Y](z)->z.get}
B2:A{.m[Y](z)->z.beer[Y]}
"""));}

@Test void inferAlpha_Rename_SingleSuper_UserNamesWin(){ okI("""
p.Box[K:imm]:{'this .get:K@p.Box;}
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.B:p.A{'this .id[T:imm](p.Box[T]):T@p.B;\
(b)->b:p.Box[T].get[imm]():T;}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X](x:Box[X]):X}
B:A{.id[T](b:Box[T])->b.get}
"""));
}

@Test void inferAlpha_Rename_SwapOrderInOverride(){ okI("""
p.A:{'this .pick[X:imm,Y:imm](p.Pair[X,Y]):Y@p.A;}
p.Pair[AA:imm, BB:imm]:{'this .fst:AA@p.Pair; .snd:BB@p.Pair;}
p.B:p.A{'this .pick[U:imm,V:imm](p.Pair[V,U]):V@p.B;\
(p)->p:p.Pair[V,U].fst[imm]():V;}
""", List.of("""
Pair[AA,BB]:{.fst:AA;.snd:BB;}
A:{.pick[X,Y](p:Pair[X,Y]):Y}
B:A{.pick[U,V](p:Pair[V,U])->p.fst}
"""));
}

@Test void inferAlpha_MultiSuper_SameBounds_SameMeaning_DifferentNames(){ okI("""
p.Box[K:imm]:{'this .get:K@p.Box;}
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.C:{'this .id[Y:imm](p.Box[Y]):Y@p.C;}
p.D:p.A, p.C{'this .id[X:imm](p.Box[X]):X@p.D;}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X:imm](x:Box[X]):X}
C:{.id[Y:imm](y:Box[Y]):Y}
D:A,C{}
"""));
}

@Test void inferAlpha_DefaultImplVsAbstract_PickAlignedImpl(){ okI("""
p.Box[K:imm]:{'this .get:K@p.Box;}
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.C:{'this .id[Y:imm](p.Box[Y]):Y@p.C;(y)->y:p.Box[Y].get[imm]():Y;}
p.D:p.A, p.C{'this .id[X:imm](p.Box[X]):X@p.C;}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X](x:Box[X]):X}
C:{.id[Y](y:Box[Y]):Y->y.get} // has impl
D:A,C{} // merge supertypes; impl origin should be C after alignment
"""));
}

@Test void abcd(){okI("""
p.GG[A:imm, B:imm]:{'this\
 .apply[C:imm,D:imm](A,B,C):D@p.GG;}
p.KK:{'_ .k[K:imm]:K@p.KK;\
->this:?.withGG[C,D](p.A_KK:$?{'_\
 ? [?](?,?,?):?@!;\
 (a, b, c)->p.Any:?!():?;}:?):K;}
p.User:{'this\
 .withGG[A1:imm,B1:imm](p.GG[A1,B1]):p.User@p.User;\
 .foo1[C:imm,D:imm]:p.User@p.User;\
->this:p.User.withGG[imm,C,D](p.A_User:p.GG[C,D]{'_\
 imm .apply[A_C:imm,A_D:imm](A_C,A_D,A_C):A_D@p.A_User;\
 (a, b, c)->p.Any:p.Any![imm,A_D]():A_D;}:p.GG[C,D]):p.User;\
 .foo2[C:imm,D:imm]:p.User@p.User;->p.KK:{'_\
 imm .k[K:imm]:K@p.KK;\
 .k()->this:p.User.withGG[imm,C,D](p.A_KK:p.GG[C,D]{'_\
 imm .apply[B_C:imm,B_D:imm](B_C,B_D,B_C):B_D@p.A_KK;\
 (a, b, c)->p.Any:p.Any![imm,B_D]():B_D;\
}:p.GG[C,D]):p.User;\
}:p.KK.k[imm,p.User]():p.User;}
p.Any:{'this ![T:imm]:T@p.Any;->p.Any:p.Any![imm,T]():T;}
p.Baba[C:imm, D:imm]:p.GG[p.Any,p.Any]{'this\
 .apply[A_C:imm,A_D:imm](p.Any,p.Any,A_C):A_D@p.GG;}
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
p.Conv:{'this .apply[S1:imm,S2:imm](S1):S2@p.Conv;}
p.B:p.A{'this .use[U1:imm,V1:imm](U1,p.Conv):V1@p.B;\
(x, c)->c:p.Conv.apply[imm,U1,V1](x:U1):V1;}
""", List.of("""
Conv:{ .apply[S1,S2](s:S1):S2 }
A:{ .use[X1,Y1](x:X1,c:Conv):Y1 }
B:A{
  .use[U1,V1](x:U1,c:Conv):V1 -> c.apply[U1,V1](x)
}
"""));}

@Test void boundMustAlphaSimple(){okI("""
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1[X:imm]:p.A{'this\
 .m[A_X:imm](p.Foo[A_X]):A_X@p.B1;\
(z)->z:p.Foo[A_X].get[imm]():A_X;}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1[X]:A{.m(z)->z.get}
"""));}

@Test void inLineAnonObject1(){okI("""
p.Bla:{'_ .bla:p.User@p.Bla;->p.User:p.User;}
p.User:{'this\
 .m:p.User@p.User;\
->p.Bla:{'_\
 imm .bla:p.User@p.Bla;\
 .bla()->p.User:p.User;\
}:p.Bla.bla[imm]():p.User;}
""",List.of("""
User:{.m:User->
 Bla:{.bla:User->User;}.bla
}
"""));}

@Test void inLineAnonObject2(){okI("""
p.User:{'this\
 .m:p.User@p.User;\
->p.A_User:{'_ imm\
 .bla:p.User@p.A_User;\
 .bla()->p.User:p.User;}:p.A_User.bla[imm]():p.User;}
p.A_User:{'_ .bla:p.User@p.A_User;->p.User:p.User;}
""",List.of("""
User:{.m:User->
 {.bla:User->User;}.bla
}
"""));}

@Test void regressionMethodHeaderAndGet1(){okI("""
p.A:{'this}
p.User:{'this\
 .m:p.A@p.User;\
->p.A_User:p.A{'_ imm .m:p.A@p.A_User; .m()->p.A:p.A;}:p.A;}
""",List.of("""
A:{}
User:{ .m:A->{ .m:A->A;}; }
"""));}

@Test void regressionMethodHeaderAndGet2(){failI("""
In file: [###]/in_memory0.fear

003| User:{ .m:A->{ .m->A;}; }
   |                ^^^^^^^^^^

While inspecting literal implementing type "p.A"
Can not infer return type of method ".m:?".
No supertype has a method named ".m" with 0 parameters.
Error 9  WellFormedness
""",List.of("""
A:{}
User:{ .m:A->{ .m->A;}; }
"""));}

@Test void badSealedOutNoInference(){failI("""
In file: [###]/in_memory0.fear

003| User:base.Void{ .m:A->A }
   | ^^^^^

While inspecting type declaration "User"
Type "User" implements sealed type"base.Void".
Sealed types can only be implemented in ther own package.
Type "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9  WellFormedness
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
Type "User" implements sealed type"base.Void".
Sealed types can only be implemented in ther own package.
Type "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9  WellFormedness
""",List.of("""
A:{}
User:base.Void{}
"""));}

@Test void badSealedOutInferenceUsed(){failI("""
In file: [###]/in_memory0.fear

003| User:Void{ .m:A->A }
   | ^^^^^

While inspecting type declaration "User"
Type "User" implements sealed type"base.Void".
Sealed types can only be implemented in ther own package.
Type "User" is defined in package "p".
Type "Void" is defined in package "base".
Error 9  WellFormedness
""",importMini,List.of("""
A:{}
User:Void{ .m:A->A }
"""));}

@Test void badSealedOutInferenceInner(){failI("""
In file: [###]/in_memory0.fear

003| User:{ .m:base.Void->{ .m:A->A;}; }
   | ^^^^^^

While inspecting literal implementing type "base.Void"
Literal implementing type "base.Void" implements sealed type"base.Void".
Sealed types can only be implemented in ther own package.
Literal implementing type "base.Void" is defined in package "p".
Type "Void" is defined in package "base".
Error 9  WellFormedness
""",List.of("""
A:{}
User:{ .m:base.Void->{ .m:A->A;}; }
"""));}

//This instead should pass, to allow True/False as values
@Test void badSealedOutInferenceInnerEmpty(){okI("""
p.A:{'this}
p.User:{'this\
 .m:base.Void@p.User;\
->base.Void:base.Void;}
""",List.of("""
A:{}
User:{ .m:base.Void->{ }; }
"""));}

@Test void expandDeclarationStages(){okI("""
p.A:{'this .m:base.Nat@p.A;->base.1:base.Nat;}
p.B:p.A{'this .m:base.Nat@p.B;->base.2:base.Nat;}
p.C:p.A, p.B{'this .m:base.Nat@p.B;}
""",List.of("""
A: { .m():base.Nat -> 1; }
B:A{ .m():base.Nat -> 2; }
C:B{}
"""));}

//The Err below is ok, associated to t:Err and not impacting the method signature
//it is produced by subtype read/imm T > T not being considered
@Test void genericInterfaces(){okI("""
p.Box[T:imm,mut,read]:{'this\
 mut .expose:T@p.Box;\
 read .get:read/imm T@p.Box;}
p.MakeBox:{'this\
 #[T:imm,mut,read](T):mut p.Box[T]@p.MakeBox;\
(t)->mut p.A_Make:p.Box[T]{'_\
 mut .expose:T@p.A_Make;\
 .expose()->t:Err;\
 read .get:read/imm T@p.A_Make;\
 .get()->t:Err;}:mut p.Box[T];}
p.MyB:p.Box[p.MakeBox]{'this\
 .foo:p.MyB@p.MyB;\
->p.MyB:p.MyB;\
 mut .expose:p.MakeBox@p.Box;\
 read .get:p.MakeBox@p.Box;}
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
p.Box[###]
p.MakeBox:[###]
p.A4[X:read]:p.Box[X]{'this\
 mut .expose:X@p.Box; read .get:read/imm X@p.Box;}
p.A3[X:mut]:p.Box[X]{'this\
 mut .expose:X@p.Box; read .get:read/imm X@p.Box;}
p.A1:p.Box[p.MakeBox]{'this\
 mut .expose:p.MakeBox@p.Box; read .get:p.MakeBox@p.Box;}
p.A2[X:imm]:p.Box[X]{'this\
 mut .expose:X@p.Box; read .get:read/imm X@p.Box;}
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
p.User:{'this\
 read .idX[X:imm](X):X@p.User;\
 read .idReadX[X:imm](X):read/imm X@p.User;\
 read .idBox[X:imm](X):p.Box[X]@p.User;}
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
p.A:{'this\
 .a:p.A@p.A;->p.A:p.A;\
 read .a:p.A@p.A;->p.A:p.A;\
 mut .a:p.A@p.A;->p.A:p.A;}
p.IdUser:{'this\
 .m1(p.A):p.A@p.IdUser;(x)->x:p.A.a[imm]():p.A;\
 .m2(read p.A):p.A@p.IdUser;(x)->x:read p.A.a[read]():p.A;\
 .m3(mut p.A):p.A@p.IdUser;(x)->x:mut p.A.a[mut]():p.A;\
 .m4(iso p.A):p.A@p.IdUser;(x)->x:iso p.A.a[mut]():p.A;\
 .m5(readH p.A):p.A@p.IdUser;(x)->x:readH p.A.a[read]():p.A;\
 .m6(mutH p.A):p.A@p.IdUser;(x)->x:mutH p.A.a[mut]():p.A;}
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

//TODO: this correctly shows that we can override a user defined type
//.beer[imm,X] becomes .beer[imm,Err]
//we will then merge back the user defined types when creating the core 
@Test void boundMustAlpha(){okI("""
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B2[X:imm]:p.A{'this\
 .m[A_X:imm](p.Foo[A_X]):A_X@p.B2;\
(z)->z:p.Foo[A_X].beer[imm,Err]():Err;}
p.B1[X:imm]:p.A{'this\
 .m[A_X:imm](p.Foo[A_X]):A_X@p.B1;\
(z)->z:p.Foo[A_X].get[imm]():A_X;}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1[X]:A{.m(z)->z.get}
B2[X]:A{.m(z)->z.beer[X]}
"""));}
//The above could be solved by comparing the input and the result on the top level inference steps.
//arguably, this could be applied when making the transition inference->core
//TODO: when committing to class table consider replacing all the bodies with Void or Magic! to avoid worst case shenario quadratic memory consumption.

//TODO: if some error about rc disagreement can not be triggered any more, they should become asserts
//search for 'Reference capability disagreement'
}
