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
import inferenceGrammarB.Declaration;
import inferenceGrammarB.M;
import utils.Bug;
import utils.Push;

public record InjectionSteps(Methods meths, ArrayList<Declaration> ds,HashMap<TName,Declaration> dsMap){
  public static List<Declaration> steps(Methods meths, List<Declaration> in){
    HashMap<TName,Declaration> dsMap= new HashMap<>();
    for (var d:in){ dsMap.put(d.name(), d); }
    var s= new InjectionSteps(meths,new ArrayList<>(in),dsMap);
    //ds.size will grow during iteration
    List<Declaration> res= new ArrayList<>();
    for (int i= 0; i < s.ds.size(); i += 1){ res.add(stepDec(s, s.ds.get(i))); }    
    return res;
  }
  private static Declaration stepDec(InjectionSteps s, Declaration di){
    var ms= di.ms().stream().map(m->{
      if (m.e().isEmpty()){ return m; }
      var e= m.e().get();
      List<IT> thisTypeTs= di.bs().stream().<IT>map(b->b.x()).toList();
      var thisType= new IT.RCC(m.sig().rc(),new IT.C(di.name(),thisTypeTs));
      E ei= meet(e,TypeRename.tToIT(m.sig().ret()));      
      Gamma g= Gamma.of(m.xs(),TypeRename.tToIT(m.sig().ts()),di.thisName(),thisType);
      ei= s.nextStar(g, ei);
      return new M(m.sig(),m.xs(),Optional.of(ei));
    }).toList();
    return di.withMs(ms);
  }
  static E meet(E e, IT t){ return e.withT(meet(e.t(),t)); }
  static IT meet(IT t1, IT t2){ 
    if (t2 == IT.U.Instance){ return t1; }
    if (t1 == IT.U.Instance){ return t2; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.rc().equals(x2.rc())){ return IT.Err.Instance; }
      if (!x1.c().name().equals(x2.c().name())){ return IT.Err.Instance; }
      if (x1.c().ts().size() != x2.c().ts().size()){ return IT.Err.Instance; }//TODO: or assert?
      var ts= meet(x1.c().ts(),x2.c().ts());
      return new IT.RCC(x1.rc(),new IT.C(x1.c().name(),ts));
    }
    if (t1.equals(t2)){ return t1; }
    return IT.Err.Instance;
    }
  static List<IT> meet(List<IT> t1, List<IT> t2){
    assert t1.size() == t2.size(): "should have gone in Err before";
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
  E nextStar(Gamma g,E e){
    while (true){
      var oe= next(g,e);
      if (oe == e){ return e; }
      e= oe;  
    }
  }
  private List<E> nextStar(Gamma g, List<E> es){
    long old= g.visibleVersion();
    boolean same= true;
    var res= new ArrayList<E>(es.size());
    for (E ei:es){
      E next=nextStar(g,ei);
      same &= next == ei;
      res.add(next);
    }
    if (same && old == g.visibleVersion()){ return es; }
    return Collections.unmodifiableList(res);
  }
  E next(Gamma g, E e){ return switch (e){
    case E.X x -> nextX(g,x);
    case E.Literal l -> nextL(g,l);
    case E.Call c -> nextC(g,c);
    case E.ICall c -> nextIC(g,c);
    case E.Type t -> nextT(g,t);
  };}
  private List<String> dom(List<inferenceGrammar.B> bs){ return bs.stream().map(b->b.x().name()).toList(); }
  private IT preferred(IT.RCC type){
    var d= dsMap.get(type.c().name());
    var cs= d.cs().stream().filter(c->c.name().s().equals("base.WidenTo")).toList();
    if (cs.size() == 0){ return type; } 
    assert cs.size() == 1;//TODO: add a well formed error for this and for Sealed
    assert cs.getFirst().ts().size() == 1;
    IT wid= TypeRename.of(TypeRename.tToIT(cs.getFirst().ts().getFirst()), dom(d.bs()), type.c().ts());
    return wid;
  }
  public record MSig(RC rc, List<String> bs, List<IT> ts, IT ret){}
  private RC overloadNorm(RC rc){ return switch(rc){
    case imm->RC.imm;
    case iso->RC.mut;
    case mut->RC.mut;
    case mutH->RC.mut;
    case read->RC.read;    
    case readH->RC.read;
  };}
  private M oneFromExplicitRC(List<M> ms){
    if (ms.size() == 1){ return ms.getFirst(); }
    throw Bug.todo();
  }
  private M oneFromGuessRC(List<M> ms, RC rc){
    var readOne= ms.stream().filter(m->m.sig().rc()==RC.read).findFirst();
    if (rc== RC.read){ return readOne.orElseThrow(Bug::todo); }
    if (rc== RC.mut){
      var mutOne= ms.stream().filter(m->m.sig().rc()==RC.mut).findFirst();
      return mutOne.or(()->readOne).orElseThrow(Bug::todo);
    }
    assert rc== RC.imm;
    var immOne= ms.stream().filter(m->m.sig().rc()==RC.imm).findFirst();
    return immOne.or(()->readOne).orElseThrow(Bug::todo);
  }
  private MSig methodHeader(IT.RCC rcc, MName name,Optional<RC> favorite){
    var d= dsMap.get(rcc.c().name());
    Stream<M> ms= d.ms().stream().filter(m->m.sig().m().equals(name));
    M m= favorite
      .map(rc->oneFromExplicitRC(ms.filter(mi->mi.sig().rc().equals(rc)).toList()))
      .orElseGet(()->oneFromGuessRC(ms.toList(),overloadNorm(rcc.rc())));
    //(RC rc, List<String> bs, List<IT> ts, IT ret)
    List<String> xs= Stream.concat(d.bs().stream(),m.sig().bs().stream())
      .map(b->b.x().name()).toList();
    assert xs.stream().distinct().count() == xs.size();
    var normXs= normXs(m.sig().bs().size());
    List<String> bs= normXsStr(m.sig().bs().size());
    var ts= Push.of(rcc.c().ts(),normXs);
    List<IT> tsRes= m.sig().ts().stream()
      .map(t->TypeRename.of(TypeRename.tToIT(t),xs,ts))
      .toList();//using normXs since it could be that rcc.ts contains X in m.bs()
    IT tRet= TypeRename.of(TypeRename.tToIT(m.sig().ret()),xs,ts);
    return new MSig(m.sig().rc(),bs,tsRes,tRet);
  }
  private List<IT> normXs(int n){ return IntStream.range(0, n).<IT>mapToObj(i->new IT.X("$"+i)).toList(); }
  private List<String> normXsStr(int n){ return IntStream.range(0, n).mapToObj(i->"$"+i).toList(); }
    //TODO: could cache 0-100 qMarks
  private List<IT> qMarks(int n){ return IntStream.range(0, n).<IT>mapToObj(_->IT.U.Instance).toList(); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i->i==n?t:IT.U.Instance).toList(); }
  //-----------Metarules
  private E nextX(Gamma g, E.X x){ 
    var t1= g.get(x.name());
    var t2= x.t();
    if (t1.equals(t2)) { return x; }
    var t3= meet(t1,t2);
    g.update(x.name(),t3);
    return x.withT(t3);
  }
  private E nextT(Gamma g, E.Type t){
    var t1= preferred(t.type());
    var t2= t.t();
    if (t1.equals(t2)) { return t; }
    var t3= meet(t1,t2);
    return t.withT(t3);
  }
  private E nextIC(Gamma g, E.ICall c){
    if (c.g() == g.visibleVersion()){ return c; }
    var e= nextStar(g,c.e());
    var es= nextStar(g,c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return new E.ICall(e,c.name(),es,c.t(),c.pos(),g.visibleVersion()); }
    MSig m= methodHeader(rcc,c.name(),Optional.empty());
    List<IT> ts= qMarks(m.bs().size());
    var es1= IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i),TypeRename.of(m.ts().get(i),m.bs(),ts)))
      .toList();
    var t= meet(c.t(),TypeRename.of(m.ret(),m.bs(),ts));
    var isVal= ts.isEmpty() && e.isEV() && es.stream().allMatch(E::isEV);
    var call= new E.Call(e,c.name(),Optional.of(m.rc()),ts,es1,t,c.pos(),isVal, 0);
    return call;
  }
  private E nextC(Gamma g, E.Call c){
    if (c.isEV() || c.g() == g.visibleVersion()){ return c; }
    var e= nextStar(g,c.e());
    var es= nextStar(g, c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withG(g.visibleVersion()); }
    MSig m= methodHeader(rcc,c.name(),c.rc());
    RC rc= c.rc().orElse(m.rc());
    assert m.ts().size() == es.size();
    var targs= meet(Stream.concat(
      IntStream.range(0, c.es().size())
        .mapToObj(i->refine(m.bs(),m.ts().get(i),es.get(i).t())),
      Stream.of(refine(m.bs(),m.ret(),c.t()),c.targs())
      ).toList());
    var it= meet(c.t(),TypeRename.of(m.ret(),m.bs(),targs));
    var es1= IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i),TypeRename.of(m.ts().get(i),m.bs(),targs)))
      .toList();
    //if (e==c.e() && es == c.es() && targs==c.targs()){ return c.withG(g.visibleVersion()); }//TODO: need more work
    var isVal= e.isEV() && es.stream().allMatch(E::isEV) && targs.stream().allMatch(IT::isTV); 
    return new E.Call(e, c.name(), Optional.of(rc),targs,es1,it, c.pos(),isVal,0); 
  }
  private E nextL(Gamma g, E.Literal l){
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    if (l.isEV() || l.g() == g.visibleVersion()){ return l; }
    if (!l.infA()){ l= meths.expandLiteral(l,rcc.c()); }
    long old= g.visibleVersion();
    boolean same= true;
    var res= new ArrayList<inferenceGrammar.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    for (var mi: l.ms()){
      TSM next= nextMStar(g,l.thisName(),rcc,ts,mi);
      same &= next.m == mi & ts == next.ts;
      res.add(next.m);
      ts = next.ts;
    }
    if (same && old == g.visibleVersion()){ return l.withFlag(g.visibleVersion()); }
    var ms= Collections.unmodifiableList(res);
    IT t= new IT.RCC(rcc.rc(),new IT.C(rcc.c().name(),ts));
    return new E.Literal(l.thisName(),ms,t,l.pos(),true,0);
  }
  record TSM(List<IT> ts, inferenceGrammar.M m){}
  private TSM nextMStar(Gamma g, String thisN, IT.RCC rcc, List<IT> ts, inferenceGrammar.M m){
    IT t= new IT.RCC(rcc.rc(),new IT.C(rcc.c().name(),ts));
    g.newScope();
    g.declare(thisN, t);
    var size= m.sig().m().get().arity();
    var xs= m.impl().get().xs();
    var args= m.sig().ts();
    for(int i= 0; i < size; i += 1){
      g.declare(xs.get(i), args.get(i).get());
    }
    E e= nextStar(g,m.impl().get().e());
    //read all the vars and get args' and ret'
    g.popScope();
    //call classJoin
    //improve meth header
    //return new method
    throw Bug.todo();
  }
  /*
  M  = m[Xs](x1:T1     ..xn:Tn     ) : T0  { return e0;  }                 //step1
  M' = m[Xs](x1:T'1⊓T"1..xn:T'n⊓T"n) : typeOf(e'0)⊓ T"0 {return e'0⊓ T"0;} //step5
  Γ, this:C[Ts],x1:T1..xn:Tn⊢ e0 ==>* Γ',this:_, x1:T'1..xn:T'n ⊢ e'0     //step2
  classJoin( C[Ts], m[Xs](x1:T'1 .. xn:T'n):T'0 ) = C[Ts']                 //step3
  methodHeader(C[Ts'],m) = m[Xs](_:T"1.._:T"n):T"0                         //step4

----------------------------------------------------------- (meth)
  Γ;C[Ts] ⊢ M ==>* Γ';C[Ts'] ⊢ M'
  */
  List<IT> refine(List<String> xs,IT t, IT t1){ return switch(t){
    case IT.X x -> refineXs(xs,x,t1);
    case IT.RCX(RC _, IT.X x) -> refineXs(xs,x,t1);
    case IT.ReadImmX(IT.X x) -> refineXs(xs,x,t1);
    case IT.RCC(RC _, IT.C c) -> propagateXs(xs,c,t1);
    case IT.U _   -> qMarks(xs.size());
    case IT.Err _ -> qMarks(xs.size());
  };}
  List<IT> refineXs(List<String> xs, IT.X x, IT t1){
    var i= xs.indexOf(x.name());
    assert i != -1;//TODO: can we trigger this?
    return qMarks(i,t1,xs.size());
  }
  List<IT> propagateXs(List<String> xs, IT.C c, IT t1){
    if (!(t1 instanceof IT.RCC cc)){ throw Bug.todo(); }
    if (!cc.c().name().equals(c.name())){ throw Bug.todo(); }
    assert cc.c().ts().size() == c.ts().size();
    List<List<IT>> res=IntStream.range(0,c.ts().size())
      .mapToObj(i->refine(xs,c.ts().get(i),cc.c().ts().get(i)))
      .toList();
    return res.isEmpty()?qMarks(xs.size()):meet(res);
  }
}
/*

FJ inference

D   ::= interface C[Xs] { fMs , FMHs }
FMH ::= m[Xs](x1:FT1 .. xn:FTn):FT
fM  ::= FMH { return fe }
cM  ::= FMH { return ce }
M   ::= MH { return e  }
FT  ::= C[FTs] | X
T   ::= C[Ts]  | X | ? | Err
fe  ::= x | new C[FTs](){ fMs } | fe.m[FTs](fes) | fe.m(fes) | xs -> fe
ce  ::= x   | new C[FTs](){ cMs } | ce.m[FTs](ces)
e   ::= x:T | new C[Ts](){ Ms }:T | e.m[Ts](es):T | (xs->e):T | e.m(es):T
Γ   ::= x1:T1  .. xn:Tn

Pipeline for every method body
containing a full-expression fe under Γ (including 'this') with return FT

- e := inferenceOf(fe, FT)
- Γ ⊢ e ==>* Γ' ⊢ e //Γ and FT extracted from the method signature
- lower(ve) = ce
- Γ ⊢ ce : FT //finally, typing the method body

Obvious selectors:
- typeOf(e) = T
- withType(e,T) = e'
- methodHeader(T,m) = m[Xs](x1 : T1 .. xn : Tn) : T0
- methodHeader(e,m)= methodHeader(typeOf(e),m)
//Note: methodHeader(C[Ts],m) already applies [Xs=Ts]
Substitution: T[Xs=Ts] //standard
_______
#Define T ⊓ T' = T" and Ts ⊓ Ts' = Ts" //meet operator
- (T1..Tn) ⊓ (T'1..T'n) = (T1⊓T'1 .. Tn⊓T'n)
- ? ⊓ T = T
- T ⊓ ? = T
- X ⊓ X = X
- C[Ts] ⊓ C[Ts'] = C[Ts⊓Ts']
- T ⊓ T' = Err otherwise //that, meet is always defined
_______
#Define e ⊓ T = e'  //NOTE: we may want not to propagate Err on an e
  withType(e,typeOf(e) ⊓ T)
_______
#Define Γ ⊢/ e //read as Γ,e does not reduce
  ¬∃ Γ',e'.(Γ ⊢ e ==> Γ' ⊢ e')
_______
#Define Xs ⊢ T=T' : Ts' //sub notation used in (refine)

---------------------------------------------------(refineXs)
  X1..Xn X X'1..X'k ⊢ X=T : ?1..?n T ?1..?k
//selects an X inside Xs' by splitting Xs' as X1..Xn X X1'..Xk'

---------------------------------------------------(refine?)
  X1..Xn⊢ ?=T : ?1..?n

---------------------------------------------------(refineErr)
  X1..Xn⊢ Err=T : ?1..?n

  ∀ i∈0..n Xs ⊢ Ti=T'i  : Tsi 
--------------------------------------------------(propagateXs)
  Xs ⊢ C[T1..Tn]=C[T'1..T'n] : ?1..?n⊓Ts1⊓..⊓Tsn  //the first ?s are needed if n==0
_______
#Define classJoin(C[Ts], MH) = C[Ts1]
  classJoin(C[Ts], m[X1..Xk](_ : T1 .. _ : Tn) : T0 ) = C[Ts']
  with //~= is alpha renaming so that m has X1..Xk and Xs disj X1..Xk //needed?
  interface C[Xs] { _ IMH  _ } ~in Ds
  IMH = m[X1..Xk](_ : IT1 .. _ : ITn) : IT0
  forall i in 0..n Xs |- ITi=Ti : Tsi
  Ts' = Ts⊓Ts0⊓..⊓Tsn //ret type plus args
_______
#Define Γ ⊢ e ==>* Γ' ⊢ e' //read as reduce as much as possible
  Γ ⊢ e ==>* Γ ⊢ e if ¬∃ Γ',e' such that Γ ⊢ e ==> Γ' ⊢ e' 
  Γ ⊢ e ==>* Γ ⊢ e if Γ ⊢ e ==> Γ ⊢ e
  Γ ⊢ e ==>* Γ" ⊢ e" if Γ ⊢ e ==> Γ' ⊢ e' and Γ' ⊢ e' ==>* Γ" ⊢ e"   
_______
#Define Γ ⊢ e ==> Γ' ⊢ e'

//NOTE: we may want not to propagate Err on a Γ
-------------------------------------- (x)     //loop is now handled by ==>*
  Γ, x:T1 ⊢ x:T2 ==> Γ, x:T1 ⊓ T2 ⊢ x:T1 ⊓ T2

  ∀ i∈0..n Γi ⊢ ei ==>* Γ(i+1) ⊢ e'i
  methodHeader(e'0,m) undefined// may be typeOf(e'0) not of form C[_], or m not exists
-------------------------------------- (call)
  Γ0 ⊢ e0.m(e1..en):T ==> Γ(i+1) ⊢ e'0.m(e'1..e'n):T

  ∀ i∈0..n Γi ⊢ ei ==>* Γ(i+1) ⊢ e'i
  methodHeader(e'0,m) = m[X1..Xk](_:T1.._:Tn):T0
  ∀ i∈0..n T'i = Ti[X1..Xk=?1..?k]
-------------------------------------- (callI)
  Γ0 ⊢ e0.m(e1..en):T ==> Γ(i+1) ⊢ e'0.m[?1..?k](e'1⊓T'1..e'n⊓T'n):T⊓T'0

  ∀ i∈0..n Γi ⊢ ei ==>* Γ(i+1) ⊢ e'i
  methodHeader(e'0,m) undefined
----------------------------------------------------------- (callRNope)
  Γ0 ⊢ e0.m[Ts](e1..en):T ==> Γ(n+1) ⊢ e'0.m[Ts](e'1⊓T'1..e'n⊓T'n):T

  ∀ i∈0..n Γi ⊢ ei ==>* Γ(i+1) ⊢ e'i
  methodHeader(e'0,m) = m[Xs](_:T1.._:Tn):T0
  ∀ i∈1..n Xs ⊢ Ti=typeOf(e'i) : Ts'i //args
  Xs ⊢ T0=T : Ts'0 //ret type
  Ts" = Ts ⊓ Ts'0 ⊓ .. ⊓ Ts'n  
  ∀ i∈0..n T'i = Ti[Xs=Ts"]
----------------------------------------------------------- (callR)
  Γ0 ⊢ e0.m[Ts](e1..en):T ==> Γ(n+1) ⊢ e'0.m[Ts"](e'1⊓T'1..e'n⊓T'n):T⊓T'0

  m is the only abs meth of C
  methodHeader(C[Ts],m)= m[Xs'](_:T1.._:Tn):T0  
  M = m[Xs'](x1:T1 .. xn:Tn): T0 { return e0⊓T0; }
  //NOTE: 'this' changes scope here, how to handle it?
----------------------------------------------------------- (lambda)
  Γ ⊢ (x1..xn->e0) : C[Ts] ==> Γ ⊢ new C[Ts](){ M }:C[Ts]

  there is no m  that is the only abs meth of C with n parameters
----------------------------------------------------------- (lambdaNope)
  Γ ⊢ (x1..xn->e0) : C[Ts] ==> Γ ⊢ (x1..xn->e0) : C[Ts]


  e1 = new C[Ts1    ](){ M1 ..Mn  } : C[Ts1    ]
  e2 = new C[Ts(n+1)](){ M'1..M'n } : C[Ts(n+1)]
  ∀ i∈1..n  Γi;C[Tsi] ⊢ Mi ==>* Γ(i+1);C[Ts(i+1)] ⊢ M'i
----------------------------------------------------------- (anon)
  Γ1 ⊢ e1 ==> Γ(n+1) ⊢ e2

  M  = m[Xs](x1:T1     ..xn:Tn     ) : T0  { return e0;  }                 //step1
  M' = m[Xs](x1:T'1⊓T"1..xn:T'n⊓T"n) : typeOf(e'0)⊓ T"0 {return e'0⊓ T"0;} //step5
  Γ, this:C[Ts],x1:T1..xn:Tn⊢ e0 ==>* Γ',this:_, x1:T'1..xn:T'n ⊢ e'0     //step2
  classJoin( C[Ts], m[Xs](x1:T'1 .. xn:T'n):T'0 ) = C[Ts']                 //step3
  methodHeader(C[Ts'],m) = m[Xs](_:T"1.._:T"n):T"0                         //step4

----------------------------------------------------------- (meth)
  Γ;C[Ts] ⊢ M ==>* Γ';C[Ts'] ⊢ M'

Optimizing (avoiding) re entries://not quite working?
Once a Γ ⊢ e ==>* Γ' ⊢ e' completed,
we know that Γ" ⊢ e' ==>* Γ" ⊢ e' if: //that is, no progress
  Γ0 = FV(e') //gets a gamma since syntax has x:T
  ∀ x in dom(Γ0) Γ0(x) = Γ"(x)
This also means that
Once a Γ ⊢ e ==>* Γ' ⊢ ev completed, Γ" ⊢ ev ==>* Γ1 ⊢ ev' can be emulated by:
 Γ0 = FV(ev) and ev = ev'
 Γ1 = Γ0 ⊓ Γ"

//-----------------------
//Old set up
//---------------------
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
  ∀ i∈1..n Xs,Ts ⊢ Ti -> typeOf(ei) : Ts'i
  Xs,Ts ⊢ T' -> T : Ts'
  Ts" = Ts ⊓ Ts'1 ⊓ .. ⊓ Ts'n ⊓ Ts'
  T ≠ T⊓T'0 or Ts" ≠ Ts
----------------------------------------------------------- (refine)
  Γ ⊢ e0.m[Ts](e1..en):T ==> Γ ⊢ e0.m[Ts"](e1⊓T'1..en⊓T'n):T⊓T'0

  methodHeader(C[Ts1],m) = m[Xs](_:T"1.._:T"n):T"0 
  e1 = new C[Ts1](){ vMs, M1, Ms } : C[Ts1]
  e2 = new C[Ts2](){ vMs, M2, Ms } : C[Ts2]
  M1 = m[Xs](x1:T1  .. xn:Tn)  : T0  { return e0;  }
  M2 = m[Xs](x1:T'1 .. xn:T'n) : T'0 { return e'0; }
  Γ1, x1:T1⊓T"1 .. xn:Tn⊓T"n ⊢ e0⊓T"0 ==> Γ2, x1:T'1 .. xn:T'n ⊢ e'0
  T'0 = typeOf(e'0)
  classJoin( C[Ts1], m[Xs](x1:T'1 .. xn:T'n):T'0 ) = C[Ts2]
----------------------------------------------------------- (enter)
  Γ1 ⊢ e1 ==> Γ2 ⊢ e2


*/