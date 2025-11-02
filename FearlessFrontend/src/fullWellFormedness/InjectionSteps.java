package fullWellFormedness;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import inferenceGrammar.E;
import inferenceGrammar.Gamma;
import inferenceGrammar.IT;
import inferenceGrammar.T;
import inferenceGrammarB.Declaration;
import utils.Bug;

public record InjectionSteps(ArrayList<Declaration> ds,HashMap<TName,Declaration> dsMap){
  public static List<Declaration> steps(List<Declaration> res, int steps){
    HashMap<TName,Declaration> dsMap= new HashMap<>();
    for (var d:res){ dsMap.put(d.name(), d); }
    var s= new InjectionSteps(new ArrayList<>(res),dsMap);
    //ds.size will grow during iteration
    for (int i= 0; i < s.ds.size(); i += 1){ steps = stepDec(steps, s, s.ds.get(i)); }    
    return s.ds;
  }
  private static int stepDec(int steps, InjectionSteps s, Declaration di) {
    for (var m:di.ms()){
      if (m.impl().isEmpty()){ continue; }
      E ei= meet(m.impl().get().e(),TypeRename.tToIT(m.sig().ret()));
      Gamma g= Gamma.of(m.impl().get().xs(),m.sig().ts());
      while (steps-->0){
        if(end(ei)){ break; }
        var oe= s.next(g,ei);
        if(oe == ei){ break; }
        ei= oe;
      }
    }
    return steps;
  }
  static E meet(E e, IT t){ return e.withT(meet(e.t(),t)); }
  static IT meet(IT t1, IT t2){ 
    if (t2 == IT.U.Instance){ return t1; }
    if (t1 == IT.U.Instance){ return t2; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.rc().equals(x2.rc())){ throw Bug.todo(); }
      if (!x1.c().name().equals(x2.c().name())){ throw Bug.todo(); }
      var ts= meet(x1.c().ts(),x2.c().ts());
      return new IT.RCC(x1.rc(),new IT.C(x1.c().name(),ts));
    }
    if (t1.equals(t2)){ return t1; }
    throw Bug.todo();
    }
  static List<IT> meet(List<IT> t1, List<IT> t2){
    if (t1.size() != t2.size()){ throw Bug.todo(); }
    return IntStream.range(0,t1.size())
      .mapToObj(i->meet(t1.get(i),t2.get(i)))
      .toList();
  }
  static List<IT> meet(List<List<IT>> tss){
    var first= tss.getFirst();
    int size= first.size();
    assert tss.stream().allMatch(ts->ts.size() == size);
    var res= new ArrayList<IT>(size);
    for(int i= 0; i < size; i++){
      var curr= first.get(i);
      for(int j= 1; j < tss.size(); j++){
        curr= meet(curr,tss.get(j).get(i));
      }
      res.add(curr);
    }
    return Collections.unmodifiableList(res);
  }
  static boolean end(E e){ return e.isEV(); }
  
  E next(Gamma g, E e){ return switch (e){
    case E.X x -> nextX(g,x);
    case E.Literal l -> nextL(g,l);
    case E.Call c -> nextC(g,c);
    case E.ICall c -> nextIC(g,c);
    case E.Type t -> nextT(g,t);
  };}
  private E nextX(Gamma g, E.X x){ 
    var t1= g.get(x.name());
    var t2= x.t();
    if (t1.equals(t2)){ return x; }
    var t3= meet(t1,t2);
    g.update(x.name(),t3);
    return x.withT(t3);
  }
  private List<String> dom(List<inferenceGrammar.B> bs){ return bs.stream().map(b->b.x().name()).toList(); }
  private IT preferred(T.RCC type){
    var d= dsMap.get(type.c().name());
    var cs= d.cs().stream().filter(c->c.name().s().equals("base.WidenTo")).toList();
    if (cs.size() == 0){ return TypeRename.tToIT(type); } 
    assert cs.size() == 1;//TODO: add a well formed error for this and for Sealed
    assert cs.getFirst().ts().size() == 1;
    T wid= TypeRename.of(cs.getFirst().ts().getFirst(), dom(d.bs()), type.c().ts());
    return TypeRename.tToIT(wid);
  }
  private E nextT(Gamma g, E.Type t){
    var t1= preferred(t.type());
    var t2= t.t();
    if (t1.equals(t2)) { return t; }
    var t3= meet(t1,t2);
    return t.withT(t3);
  }
  E nextStar(Gamma g,E e){
    while (true){
      var oe= next(g,e);
      if (oe == e){ return e; }
      e= oe;  
    }
  }//TODO: could remove all Optional<E> and use ret == input to signal no output
  private E nextIC(Gamma g, E.ICall c){
    if (c.g() == g.visibleVersion()){ return c; }
    var e= nextStar(g,c.e());
    if (!(e.t() instanceof IT.RCC rcc)){ return new E.ICall(e,c.name(),c.es(),c.t(),c.pos(),g.visibleVersion()); }
    MSig m= methodSig(rcc,c.name(),Optional.empty());
    List<IT> ts= qMarks(m.bs().size());
    var call= new E.Call(e,c.name(),Optional.of(m.rc()),ts,c.es(),c.t(),c.pos(),false, 0);
    return nextC(g,call);
  }
  //TODO: could cache 0-100 qMarks
  private List<IT> qMarks(int n){ return IntStream.range(0, n).<IT>mapToObj(_->IT.U.Instance).toList(); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i->i==n?t:IT.U.Instance).toList(); }
  private E nextC(Gamma g, E.Call c){
    if (c.isEV() || c.g() == g.visibleVersion()){ return c; }
    var e= nextStar(g,c.e());
    var es= c.es().stream().map(ei->nextStar(g,ei)).toList();
    if (! (c.e().t() instanceof IT.RCC rcc)){ return c.withG(g.visibleVersion()); }
    MSig m= methodSig(rcc,c.name(),c.rc());
    RC rc= c.rc().orElse(m.rc());
    assert m.ts().size() == es.size();
    List<List<IT>> tss= Stream.concat(
      IntStream.range(0, c.es().size())
        .mapToObj(i->refine(m.bs(),c.targs(),m.ts().get(i),es.get(i).t())),
      Stream.of(refine(m.bs(),c.targs(),m.ret(),c.t()),c.targs())
      ).toList();
    var targs= meet(tss);
    var it= c.t();//TODO: this needs to be met with m.ret()[m.bs()/targs]
    //then all es met with m.ts()[m.bs()/targs]
    var isVal= e.isEV() && es.stream().allMatch(E::isEV) && targs.stream().allMatch(IT::isTV); 
    return new E.Call(e, c.name(), Optional.of(rc),c.targs(),es,it, c.pos(),isVal,g.visibleVersion()); 
  }
  public record MSig(RC rc, List<String> bs, List<IT> ts, IT ret){}
  private MSig methodSig(IT.RCC rcc, MName name,Optional<RC> favorite){
    //TODO: will use the rc of t, or favorite to select overload
    var d= dsMap.get(rcc.c().name());
    var ms= d.ms().stream().filter(m->m.sig().m().equals(name)).toList();//TODO: could be findAny but list helps debugging
    //TODO: there can be more then one, one for each RC of the receiver
    //We need to update the 5a inference for it, then update here
    //Remember that a method with name and implementation but no RC can be desugared to satisfy
    //multiple methods with same name and different RC.
    if (ms.size() != 1){ throw Bug.todo(); }
    //var bs=dom(m.bs());
    var n= ms.getFirst().sig().bs().size();
    throw Bug.todo();
  }
  private E nextL(Gamma g, E.Literal c){ throw Bug.todo(); }

  List<IT> refine(List<String> xs, List<IT> ts, IT t, IT t1){ return switch(t){
    case IT.X x -> refineXs(xs,ts,x,t1);
    case IT.RCX(RC _, IT.X x) -> refineXs(xs,ts,x,t1);
    case IT.ReadImmX(IT.X x) -> refineXs(xs,ts,x,t1);
    case IT.RCC(RC _, IT.C c) -> propagateXs(xs,ts,c,t1);
    case IT.U _ -> qMarks(xs.size());
  };}
  List<IT> refineXs(List<String> xs, List<IT> ts, IT.X x, IT t1){
    var i= xs.indexOf(x.name());
    assert i != -1;//TODO: can we trigger this?
    return qMarks(i,t1,xs.size());
  }
  List<IT> propagateXs(List<String> xs, List<IT> ts, IT.C c, IT t1){
    if (!(t1 instanceof IT.RCC cc)){ throw Bug.todo(); }
    if (!cc.c().name().equals(c.name())){ throw Bug.todo(); }
    assert cc.c().ts().size() == c.ts().size();
    List<List<IT>> res=IntStream.range(0,c.ts().size())
      .mapToObj(i->refine(xs,ts,c.ts().get(i),cc.c().ts().get(i)))
      .toList();
    return meet(res);
  }
}
/*  
_______
#Define Xs,Ts ⊢ T -> T' : Ts' //sub notation used in (refine)

---------------------------------------------------(refineXs)
  X1..Xn X X'1..X'k,Ts ⊢ X -> T : ?1..?n T ?1..?k
//selects an X inside Xs' by splitting Xs' as X1..Xn X X1'..Xk'

  ∀ i∈0..n Xs,Ts ⊢ Ti  -> T'i  : Tsi 
--------------------------------------------------(propagateXs)
  Xs,Ts ⊢ C[T1..Tn] -> C[T'1..T'n] : Ts1⊓..⊓Tsn



*/  

/*

FJ inference

D   ::= interface C[Xs] { fMs , VMHs }
VMH ::= m[Xs](x1:VT1 .. xn:VTn):VT
fM  ::= VMH { return fe }
cM  ::= VMH { return ce }
M   ::= VMH { return e  }
VM  ::= m[Xs](x1:VT1 .. xn:VTn):VT { return ve }
VT  ::= C[VTs] | X
T   ::= C[Ts]  | X | ?
fe  ::= x | new C[VTs](){ fMs } | fe.m[VTs](fes) | fe.m(fes) | xs -> fe
ce  ::= x | new C[VTs](){ cMs } | ce.m[VTs](ces)
e   ::= x:T | new C[Ts](){ Ms }:T | e.m[Ts](es):T | (xs->e):T | e.m(es):T
ve  ::= x:VT | new C[VTs](){ VMs }:VT | ve.m[VTs](ves):VT
VΓ  ::= x1:VT1 .. xn:VTn
Γ   ::= x1:T1  .. xn:Tn
//Implicit non terminals
Xs  ::= X1..Xn
Ts  ::= T1..Tn
VTs ::= VT1..VTn
es  ::= e1..en
//Note: e1..en is empty if n=0; e0..en instead has at least 1 element
//Γ and VΓ are maps, so the order of elements is irrelevant

Pipeline for every method body
containing a full-expression fe under VΓ with return VT

- e := inferenceOf(fe, VT)
- VΓ ⊢ e ==>⋆ Γ' ⊢ ve //VΓ extracted from the method signature
- lower(ve) = ce
- VΓ ⊢ ce : VT //finally, typing the method body

Obvious selectors:
- typeOf(e) = T
- withType(e,T) = e'
- methodHeader(T,m) = m[Xs](x1 : T1 .. xn : Tn) : T0
- methodHeader(e,m)= methodHeader(typeOf(e),m)
//Note: methodHeader(C[Ts],m) already applies [Xs=Ts]
Substitution: T[Xs=Ts] //standard

#Define e ⊓ T = e'
  withType(e,typeOf(e) ⊓ T)

#Define Γ ⊢/ e //read as Γ,e does not reduce
  ¬∃ Γ',e'.(Γ ⊢ e ==> Γ' ⊢ e')

#Define T ⊓ T' = T" and Ts ⊓ Ts' = Ts" //meet operator
- (T1..Tn) ⊓ (T'1..T'n) = (T1⊓T'1 .. Tn⊓T'n)
- ? ⊓ T = T
- T ⊓ ? = T
- X ⊓ X = X
- C[Ts] ⊓ C[Ts'] = C[Ts⊓Ts']
//Note: if X ≠ X' then X ⊓ X' is undefined
//Expected properties (where defined): commutative, idempotent, associative

Rules for Γ ⊢ e ==> Γ' ⊢ e'

  T1 ⊓ T2 = T3
  T1 ≠ T2
-------------------------------------- (x)
  Γ, x:T1 ⊢ x:T2 ==> Γ, x:T3 ⊢ x:T3


  Γ ⊢ e0 ==> Γ' ⊢ e0'
------------------------------------------ (ctx-recv-bracket)
  Γ ⊢ e0.m[Ts](es):T ==> Γ' ⊢ e0'.m[Ts](es):T


  Γ ⊢ e0 ==> Γ' ⊢ e0'
-------------------------------------- (ctx-recv-plain)
  Γ ⊢ e0.m(es):T ==> Γ' ⊢ e0'.m(es):T


  Γ⊢/e
  methodHeader(e,m) = m[X1..Xn](_:T1.._:Tk):T0
  ∀ i∈0..n T'i = Ti[X1..Xn=?1..?n]
-------------------------------------------------- (get[_])
  Γ ⊢ e.m(e1..ek):T ==> Γ ⊢ e.m[?1..?n](e1⊓T'1..ek⊓T'k):T⊓T'0

  ∀ i∈0..n Γ⊢/ei
  methodHeader(e0,m)= m[Xs](_:T1.._:Tn _:T _:_):_
  Γ ⊢ e ==> Γ' ⊢ e'
-------------------------------------------------- (ctx-arg)
  Γ ⊢ e0.m[Ts](e1..en e es'):T0 ==> Γ' ⊢ e0.m[Ts](e1..en e' es'):T0

  m is the only abs meth of C
  methodHeader(C[Ts],m)= m[Xs’](_:T1.._:Tn):T0  
  M = m[Xs’](x1:T1 .. xn:Tn): T0 { return e0⊓T0; }
----------------------------------------------------------- (lambda)
  Γ ⊢ (x1..xn->e0) : C[Ts] ==> Γ ⊢ new C[Ts](){ M }:C[Ts]

  methodHeader(e0,m) = m[Xs](_ : T1 .. _ : Tn) : T0
  ∀ i∈0..n Γ⊢/ei
  ∀ i∈0..n T'i = Ti[Xs=Ts"]
  ∀ i∈1..n Xs,Ts ⊢ Ti -> typeOf(ei) : Tsi'
  Xs,Ts ⊢ T' -> T : Ts'
  Ts" = Ts ⊓ Ts1 ⊓ .. ⊓ Tsn ⊓ Ts'
  T ≠ T⊓T'0 or Ts" ≠ Ts
----------------------------------------------------------- (refine)
  Γ ⊢ e0.m[Ts](e1..en):T ==> Γ ⊢ e0.m[Ts"](e1⊓T'1..en⊓T'n):T⊓T'0
_______
#Define Xs,Ts ⊢ T -> T' : Ts' //sub notation used in (refine)

---------------------------------------------------(refineXs)
  X1..Xn X X'1..X'k,Ts ⊢ X -> T : ?1..?n T ?1..?k
//selects an X inside Xs' by splitting Xs' as X1..Xn X X1'..Xk'

  ∀ i∈0..n Xs,Ts ⊢ Ti  -> T'i  : Tsi 
--------------------------------------------------(propagateXs)
  Xs,Ts ⊢ C[T1..Tn] -> C[T'1..T'n] : Ts1⊓..⊓Tsn

//--- back to metarules for small step inference ---

  e1 = new C[Ts1](){ vMs, M1, Ms } : C[Ts1]
  e2 = new C[Ts2](){ vMs, M2, Ms } : C[Ts2]
  M1 = m[Xs](x1:T1  .. xn:Tn)  : T0  { return e0;  }
  M2 = m[Xs](x1:T'1 .. xn:T'n) : T'0 { return e'0; }
  Γ1, x1:T1 .. xn:Tn ⊢ e0 ==> Γ2, x1:T'1 .. xn:T'n ⊢ e'0
  T'0 = typeOf(e'0)
  classJoin( C[Ts1], m[Xs](x1:T'1 .. xn:T'n):T'0 ) = C[Ts2]
----------------------------------------------------------- (enter)
  Γ1 ⊢ e1 ==> Γ2 ⊢ e2

//Ds and thus methodHeader(e,m) change after this step?!?!
//(fearless only)

_______
#Define classJoin(C[Ts], MH) = C[Ts1]
  classJoin(C[Ts], m[X1..Xk](_ : T1 .. _ : Tn) : T0 ) = C[Ts']
  with
  interface C[Xs] { _ IMH  _ } ~in Ds
  //~= is alpha renaming so that m has X1..Xk and Xs disj X1..Xk
  IMH = m[X1..Xk](_ : IT1 .. _ : ITn) : IT0
  Xs disjoint X1..Xk
  forall i in 0..n Xs,Ts |- ITi -> Ti : Tsi
  Ts' = Ts⊓Ts0⊓..⊓Tsn //ret type plus args




*/