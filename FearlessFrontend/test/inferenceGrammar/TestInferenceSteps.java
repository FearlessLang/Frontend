package inferenceGrammar;

import java.util.List;

import org.junit.jupiter.api.Disabled;
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
 imm .match[G_R:imm](p.StackMatch[T,G_R]):G_R@p.Stack;\
 .match(m)->m:p.StackMatch[T,G_R].elem[imm](e:T,this:p.Stack[T]):G_R;\
 imm .fold[H_R:imm](H_R,base.F[H_R,T,H_R]):H_R@p.Stack;\
 .fold(start, f)->f:base.F[H_R,T,H_R]#[read](this:p.Stack[T].fold[imm,H_R](start:H_R,f:base.F[H_R,T,H_R]):H_R,e:T):H_R;\
 imm .map[J_R:imm](base.F[T,J_R]):p.Stack[J_R]@p.Stack;\
 .map(f)->this:p.Stack[T].map[imm,J_R](f:base.F[T,J_R]):p.Stack[J_R]\
+[imm](f:base.F[T,J_R]#[read](e:T):J_R):p.Stack[J_R];\
 imm .filter(base.F[T,base.Bool]):p.Stack[T]@p.Stack;\
 .filter(f)->f:base.F[T,base.Bool]#[read](e:T):base.Bool\
.if[imm,p.Stack[T]](mut p.C_Stac:base.ThenElse[p.Stack[T]]{'_\
 mut .then:p.Stack[T]@base.ThenElse;\
 .then()->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T]\
+[imm](e:T):p.Stack[T];\
 mut .else:p.Stack[T]@base.ThenElse;\
 .else()->this:p.Stack[T].filter[imm](f:base.F[T,base.Bool]):p.Stack[T];\
}:mut base.ThenElse[p.Stack[T]]):p.Stack[T];}:p.Stack[T];}
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

@Test void boundChangesName(){okI("""
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1:p.A{'this\
 .m[Y:imm](p.Foo[Y]):Y@p.B1;\
(z)->z:p.Foo[Y].get[imm]():Y;}
p.B2:p.A{'this\
 .m[Y:imm](p.Foo[Y]):Y@p.B2;\
(z)->z:p.Foo[Y].beer[imm,Y]():Y;}
p.Foo[K:imm]:{'this\
 .get:K@p.Foo;\
 .beer[G:imm]:G@p.Foo;}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1:A{.m[Y](z)->z.get}
B2:A{.m[Y](z)->z.beer[Y]}
"""));}

@Test void inferAlpha_Rename_SingleSuper_UserNamesWin(){ okI("""
p.A:{'this .id[X:imm](p.Box[X]):X@p.A;}
p.B:p.A{'this .id[T:imm](p.Box[T]):T@p.B;\
(b)->b:p.Box[T].get[imm]():T;}
p.Box[K:imm]:{'this .get:K@p.Box;}
""", List.of("""
Box[K]:{.get:K;}
A:{.id[X](x:Box[X]):X}
B:A{.id[T](b:Box[T])->b.get}
"""));
}

@Test void inferAlpha_Rename_SwapOrderInOverride(){ okI("""
p.A:{'this .pick[X:imm,Y:imm](p.Pair[X,Y]):Y@p.A;}
p.B:p.A{'this .pick[U:imm,V:imm](p.Pair[V,U]):V@p.B;\
(p)->p:p.Pair[V,U].fst[imm]():V;}
p.Pair[AA:imm, BB:imm]:{'this .fst:AA@p.Pair; .snd:BB@p.Pair;}
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
p.Any:{'this ![T:imm]:T@p.Any;->p.Any:p.Any![imm,T]():T;}
p.Baba[C:imm, D:imm]:p.GG[p.Any,p.Any]{'this\
 .apply[A_C:imm,A_D:imm](p.Any,p.Any,A_C):A_D@p.GG;}
p.GG[A:imm, B:imm]:{'this\
 .apply[C:imm,D:imm](A,B,C):D@p.GG;}
p.KK:{'_ .k[K:imm]:K@p.KK;\
->this:?.withGG[C,D](p.A_KK:$?{'_\
 ? [?](?,?,?):?@!;\
 (a, b, c)->p.Any:?!():?;}:?):K;}
p.User:{'this\
 .withGG[A1:imm,B1:imm](p.GG[A1,B1]):p.User@p.User;\
 .foo1[C:imm,D:imm]:p.User@p.User;\
->this:p.User.withGG[imm,Err,Err](p.A_User:p.GG[C,D]{'_\
 imm .apply[A_C:imm,A_D:imm](Err,Err,A_C):A_D@p.GG;\
 (a, b, c)->p.Any:p.Any![imm,A_D]():A_D;}:p.GG[Err,Err]):p.User;\
 .foo2[C:imm,D:imm]:p.User@p.User;\
->p.KK:{'_ ? .k[K:imm]:K@!;\
 .k()->this:?.withGG[C,D](p.A_KK:$?{'_\
 ? [?](?,?,?):?@!;\
 (a, b, c)->p.Any:?!():?;}:?):?;}:?.k[p.User]():p.User;}
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
//-------------
@Disabled @Test void inferAlpha_GenericMethod_LambdaImplements_Generic_OverrideDifferentNames(){okI("""
""", List.of("""
Conv:{ .apply[S1,S2](s:S1):S2 }
A:{ .use[X1,Y1](x:X1,c:Conv):Y1 }
B:A{
  .use[U1,V1](x:U1,c:Conv):V1 -> c.apply[U1,V1](x)
}
"""));}

@Disabled @Test void inferAlpha_MergeTwoSupers_SameShape_DifferentNames_LambdaUsesOuterBs(){okI("""
""", List.of("""
Conv:{ .apply[S1,S2](s:S1):S2 }
A:{ .use[X1,Y1](x:X1,c:Conv):Y1 }
C:{ .use[U1,V1](u:U1,k:Conv):V1 }
D:A,C{
  .use[P1,Q1](p:P1,m:Conv):Q1 -> m.apply[P1,Q1](p)
}
"""));}

@Disabled @Test void inferAlpha_ReturnsObjectWhoseMethodIsGeneric_LambdaInsideOverride(){okI("""
""", List.of("""
Mapper:{ .map[S1,S2](s:S1):S2 }
A:{ .mk[X1,Y1]():Mapper }
B:A{
  .mk[U1,V1]():Mapper -> Mapper{
    '_
    imm .map[R1,S1](r:R1):S1@Mapper;
    .map(r)->r // instantiate later at [U1,U1] or [V1,V1], types align via alpha
  }:Mapper
}
"""));}

@Disabled @Test void inferAlpha_OverloadedGenericMethods_InSameLambda_DifferentArities(){okI("""
""", List.of("""
Ops:{
  .a[S1](s:S1):S1;
  .a[S2,T2](s:S2,t:T2):S2;
}
A:{ .mk[X1]():Ops }
B:A{
  .mk[U1]():Ops -> Ops{
    '_
    imm .a[R1](r:R1):R1@Ops;                .a(r)->r;
    imm .a[R2,S2](r:R2,s:S2):R2@Ops;        .a(r,s)->r;
  }:Ops
}
"""));}

@Disabled @Test void inferAlpha_NestedLambda_ReturnsObject_WhoseMethodReturnsObject_WithGenericMethod(){okI("""
""", List.of("""
Id:{ .id[S1](s:S1):S1 }
Maker:{ .make[X1]():Id }

A:{ .mk[Y1]():Maker }
B:A{
  .mk[U1]():Maker -> Maker{
    '_
    imm .make[R1]():Id@Maker;
    .make()->Id{
      '_
      imm .id[T1](t:T1):T1@Id;
      .id(t)->t
    }:Id
  }:Maker
}
"""));}

@Disabled @Test void inferAlpha_MergeSupers_ReturnsGenericMethodObject_OverrideRenames(){okI("""
""", List.of("""
Comb:{ .pair[S1,T1](s:S1,t:T1):Pair[S1,T1] }
Pair[A1,B1]:{ .fst:A1; .snd:B1; }

A:{ .mk[X1,Y1]():Comb }
C:{ .mk[U1,V1]():Comb }
D:A,C{
  .mk[P1,Q1]():Comb -> Comb{
    '_
    imm .pair[R1,S1](r:R1,s:S1):Pair[R1,S1]@Comb;
    .pair(r,s)->{ .fst->r; .snd->s; }
  }:Comb
}
"""));}

@Disabled @Test void inferAlpha_ClassAndMethodGenericsInteract_NoShadowing_NestedUse(){okI("""
""", List.of("""
Box[T0]:{ .get:T0 }
X:{ .lift[X1](b:Box[X1]): Box[X1] }
A[T0]:X{
  .lift[U1](b:Box[U1]): Box[U1] -> b // trivial, but exercises class T0 + method U1
}
"""));}

@Disabled @Test void inferAlpha_TransitiveImport_A_B_C_LeafRenamesAndUsesNestedGenericObject(){okI("""
""", List.of("""
Conv:{ .apply[S1,S2](s:S1):S2 }
A:{ .use[X1,Y1](x:X1,c:Conv):Y1 }
B:A{}
C:B{
  .use[U1,V1](x:U1,c:Conv):V1 -> {
    // build a helper object with its own generic method and use it
    Helper:{ .twice[R1](r:R1):R1 } // generic method
    var h = Helper{ '_ imm .twice[Q1](q:Q1):Q1@Helper; .twice(q)->q }:Helper;
    // still call the Conv generic method, making sure bs line up
    h.twice[V1]( c.apply[U1,V1](x) )
  }
}
"""));}

@Disabled @Test void inferAlpha_MultiLevel_ReturnsOverloadedGenericObject_ArityOverload(){okI("""
""", List.of("""
Ops:{
  .sel[S1](s:S1):S1;
  .sel[S2,T2](s:S2,t:T2):S2;
}
A:{ .mk[X1]():Ops }
B:A{}
C:B{
  .mk[U1]():Ops -> Ops{
    '_
    imm .sel[R1](r:R1):R1@Ops;           .sel(r)->r;
    imm .sel[R2,S2](r:R2,s:S2):R2@Ops;   .sel(r,s)->r;
  }:Ops
}
"""));}

@Disabled @Test void inferAlpha_GenericMethodCallsAnotherGenericMethod_OnParameterObject(){okI("""
""", List.of("""
Proj:{ .fst[S1,T1](p:Pair[S1,T1]):S1 }
Pair[A1,B1]:{ .fst:A1; .snd:B1; }
A:{ .left[X1,Y1](p:Pair[X1,Y1], pr:Proj):X1 }
B:A{
  .left[U1,V1](p:Pair[U1,V1], pr:Proj):U1 -> pr.fst[U1,V1](p)
}
"""));}

@Disabled @Test void inferAlpha_ReturnsGenericMethodObject_ThatCallsCallerBsInside(){okI("""
""", List.of("""
Ap:{ .ap[S1,T1](x:S1):T1 }
A:{ .mk[X1,Y1]():Ap }
B:A{
  .mk[U1,V1]():Ap -> Ap{
    '_
    imm .ap[R1,S1](r:R1):S1@Ap;
    .ap(r)->{
      // fabricate a value by bouncing through an identity object with generic method
      Id:{ .id[Q1](q:Q1):Q1 }
      Id{ '_ imm .id[W1](w:W1):W1@Id; .id(w)->w }:Id .id[S1]( /* some S1 value */ r )
    }
  }:Ap
}
"""));}

@Disabled @Test void inferAlpha_TwoSupersAgree_LeafOmitsBs_UseAgreementBs_ThenAlign(){okI("""
""", List.of("""
Conv:{ .apply[S1,S2](s:S1):S2 }
A:{ .use[X1,Y1](x:X1,c:Conv):Y1 }
C:{ .use[U1,V1](u:U1,c:Conv):V1 }
D:A,C{
  .use(x,c)-> c.apply[ /* inferred X/Y */ ](x) // omit local bs; force agreementBs then align
}
"""));}

@Disabled @Test void inferAlpha_DeepNest_3Levels_GenericMethods_AllAligned(){okI("""
""", List.of("""
L1:{ .m1[A1,B1](a:A1):B1 }
L2:{ .m2[C1,D1](c:C1,l:L1):D1 }
L3:{ .m3[E1,F1](e:E1,l:L2):F1 }

A:{ .go[X1,Y1](x:X1,l:L3):Y1 }
B:A{
  .go[U1,V1](x:U1,l:L3):V1 -> l.m3[U1,V1](x, L2{
    '_
    imm .m2[R1,S1](r:R1,l1:L1):S1@L2;
    .m2(r,l1)-> l1.m1[R1,S1](r)
  }:L2)
}
"""));
}

//---------
@Test void boundMustAlphaSimple(){okI("""
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1[X:imm]:p.A{'this\
 .m[A_X:imm](p.Foo[A_X]):A_X@p.B1;\
(z)->z:p.Foo[A_X].get[imm]():A_X;}
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
""",List.of("""
Foo[K]:{.get:K; .beer[G]:G;}
A:{.m[X](x:Foo[X]):X}
B1[X]:A{.m(z)->z.get}
"""));}

//TODO: this correctly shows that we can override a user defined type
//.beer[imm,X] becomes .beer[imm,Err]
//we will then merge back the user defined types when creating the core 
@Test void boundMustAlpha(){okI("""
p.A:{'this .m[X:imm](p.Foo[X]):X@p.A;}
p.B1[X:imm]:p.A{'this\
 .m[A_X:imm](p.Foo[A_X]):A_X@p.B1;\
(z)->z:p.Foo[A_X].get[imm]():A_X;}
p.B2[X:imm]:p.A{'this\
 .m[A_X:imm](p.Foo[A_X]):A_X@p.B2;\
(z)->z:p.Foo[A_X].beer[imm,Err]():Err;}
p.Foo[K:imm]:{'this .get:K@p.Foo; .beer[G:imm]:G@p.Foo;}
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
