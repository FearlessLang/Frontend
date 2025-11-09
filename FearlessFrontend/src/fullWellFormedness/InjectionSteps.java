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

public record InjectionSteps(Methods meths, ArrayList<Declaration> ds,HashMap<TName,Declaration> dsMap,OtherPackages other){
  public static List<Declaration> steps(Methods meths, List<Declaration> in, OtherPackages other){
    HashMap<TName,Declaration> dsMap= new HashMap<>();
    for (var d:in){ dsMap.put(d.name(), d); }
    var s= new InjectionSteps(meths,new ArrayList<>(in),dsMap,other);
    //ds.size will grow during iteration
    int size= s.ds.size();
    List<Declaration> res= new ArrayList<>();
    for (int i= 0; i < size; i += 1){ res.add(stepDec(s, s.ds.get(i))); }    
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
      return x1.withTs(ts);
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
  private List<E> meet(List<E> es, MSig m, List<IT> targs){
    boolean same= true;
    var res= new ArrayList<E>(es.size());
    for(int i= 0; i < es.size(); i += 1){
      E next= meet(es.get(i),TypeRename.of(m.ts().get(i),m.bs(),targs));
      same &= next == es.get(i);
      res.add(next);
    }
    if (same){ return es; }
    return Collections.unmodifiableList(res);
  }
  private List<E> nextStar(Gamma g, List<E> es){
    long old= g.visibleVersion();
    boolean same= true;
    var res= new ArrayList<E>(es.size());
    for (E ei:es){
      E next= nextStar(g,ei);
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
    case E.Type c -> nextT(g,c);
  };}
  private List<String> dom(List<inferenceGrammar.B> bs){ return bs.stream().map(b->b.x().name()).toList(); }
  Declaration getDec(TName name){
    var d= dsMap.get(name);
    if (d != null){ return d; }
    return other.of(name);
  }
  private IT preferred(IT.RCC type){
    var d= getDec(type.c().name());
    assert d != null : type;
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
  private Optional<M> oneFromExplicitRC(List<M> ms){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    return Optional.empty();
  }
  private Optional<M> oneFromGuessRC(List<M> ms, RC rc){
    var readOne= ms.stream().filter(m->m.sig().rc()==RC.read).findFirst();
    if (rc== RC.read){ return readOne; }
    if (rc== RC.mut){ return ms.stream().filter(m->m.sig().rc()==RC.mut).findFirst(); }
    assert rc== RC.imm;
    return ms.stream().filter(m->m.sig().rc()==RC.imm).findFirst();
  }
  private Optional<MSig> methodHeader(IT.RCC rcc, MName name,Optional<RC> favorite){
    var d= getDec(rcc.c().name());
    Stream<M> ms= d.ms().stream().filter(m->m.sig().m().equals(name));
    Optional<M> om= favorite
      .map(rc->oneFromExplicitRC(ms.filter(mi->mi.sig().rc().equals(rc)).toList()))
      .orElseGet(()->oneFromGuessRC(ms.toList(),overloadNorm(rcc.rc())));
    if (om.isEmpty()){ return Optional.empty(); }
    M m= om.get();
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
    return Optional.of(new MSig(m.sig().rc(),bs,tsRes,tRet));
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
    var t1= preferred(t.type());//TODO: preferred need to be called also on the literals
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
    Optional<MSig> om= methodHeader(rcc,c.name(),Optional.empty());
    if (om.isEmpty()){ return new E.ICall(e,c.name(),es,c.t(),c.pos(),g.visibleVersion()); }
    MSig m= om.get();
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
    if (!(e.t() instanceof IT.RCC rcc)){
      return new E.Call(e,c.name(),c.rc(),c.targs(),es,c.t(),c.pos(),false,g.visibleVersion()); 
    }
    Optional<MSig> om= methodHeader(rcc,c.name(),c.rc());
    if (om.isEmpty()){ return new E.Call(e,c.name(),c.rc(),c.targs(),es,c.t(),c.pos(),false,g.visibleVersion()); }
    MSig m= om.get();
    RC rc= c.rc().orElse(m.rc());
    assert m.ts().size() == es.size();
    var targs= meet(Stream.concat(
      IntStream.range(0, c.es().size())
        .mapToObj(i->refine(m.bs(),m.ts().get(i),es.get(i).t())),
      Stream.of(refine(m.bs(),m.ret(),c.t()),c.targs())
      ).toList());
    var it= meet(c.t(),TypeRename.of(m.ret(),m.bs(),targs));
    var es1 = meet(es, m, targs);
    if (e==c.e() && es == c.es() && targs.equals(c.targs())  && it.equals(c.t())){ return c.withFlag(g.visibleVersion()); }
    var isVal= e.isEV() && es.stream().allMatch(E::isEV) && targs.stream().allMatch(IT::isTV); 
    return new E.Call(e, c.name(), Optional.of(rc),targs,es1,it, c.pos(),isVal,0); 
  }
  private E nextL(Gamma g, E.Literal l){
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    if (l.g() == g.visibleVersion()){ return l; }
    //TODO: if has rc use preferred(T.RCC) for the type, but
    //still run the inference for the methods, not classJoin??
    //Also, if the inferred type is a value no classJoin??
    
    //TODO: when we get a fully evaluated class head, we need to 'add to declarations'
    //this will require to move from 5a to 5b. The literal 'also' stays in place, but we need the declaration
    //for this types. Also, this is where we move the this type from the impl to the outer.
    //Can this could cause 'Err' before and they would stay later??
    //if (l.isEV()){ return l; }
    if (!l.infA()){ l= meths.expandLiteral(l,rcc.c()); }
    long old= g.visibleVersion();
    boolean same= true;
    var res= new ArrayList<inferenceGrammar.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    for (var mi: l.ms()){
      TSM next= nextMStar(g,l.thisName(),rcc,ts,mi);
      same &= next.m.sig().equals(mi.sig()) & ts.equals(next.ts);
      res.add(next.m);
      ts = next.ts;
    }
    if (same && old == g.visibleVersion()){ return l.withFlag(g.visibleVersion()); }
    var ms= Collections.unmodifiableList(res);
    IT t= rcc.withTs(ts);
    return l.withMsT(ms,t,true);
  }
  record TSM(List<IT> ts, inferenceGrammar.M m){}
  private TSM nextMStar(Gamma g, String thisN, IT.RCC rcc, List<IT> ts, inferenceGrammar.M m){
    IT.RCC t= rcc.withTs(ts);
    var size= m.sig().m().get().arity();
    var xs= m.impl().get().xs();
    var args= m.sig().ts();
    g.newScope();
    g.declare(thisN, t);
    for(int i= 0; i < size; i += 1){ g.declare(xs.get(i), args.get(i).get()); }
    E e= nextStar(g,m.impl().get().e());
    args= xs.stream().map(x->Optional.of(g.get(x))).toList(); 
    var improvedSig= m.sig().refine(args, Optional.of(e.t()));
    g.popScope();
    return classJoin(t,improvedSig,m.impl());
  }
  List<IT> refine(List<String> xs,IT t, IT t1){
    if( t1 instanceof IT.U){ qMarks(xs.size()); } 
    return switch(t){
      case IT.X x -> refineXs(xs,x,t1);
      case IT.RCX(RC _, IT.X x) -> refineXs(xs,x,t1);
      case IT.ReadImmX(IT.X x) -> refineXs(xs,x,t1);
      case IT.RCC(RC _, IT.C c) -> propagateXs(xs,c,t1);
      case IT.U _   -> qMarks(xs.size());
      case IT.Err _ -> qMarks(xs.size());
    };
  }
  List<IT> refineXs(List<String> xs, IT.X x, IT t1){
    var i= xs.indexOf(x.name());
    assert i != -1;//TODO: can we trigger this?
    return qMarks(i,t1,xs.size());
  }
  List<IT> propagateXs(List<String> xs, IT.C c, IT t1){
    if (t1 instanceof IT.U || t1 instanceof IT.Err){ return qMarks(xs.size()); }
    if (!(t1 instanceof IT.RCC cc)){ throw Bug.unreachable(); }//not assert to declare cc
    if (!cc.c().name().equals(c.name())){ return qMarks(xs.size()); }
    assert cc.c().ts().size() == c.ts().size();
    List<List<IT>> res=IntStream.range(0,c.ts().size())
      .mapToObj(i->refine(xs,c.ts().get(i),cc.c().ts().get(i)))
      .toList();
    return res.isEmpty()?qMarks(xs.size()):meet(res);
  }
  //TODO: merge classJoin with the metarule
  TSM classJoin(IT.RCC rcc, inferenceGrammar.M.Sig sig, Optional<inferenceGrammar.M.Impl> impl){
    var ts= rcc.c().ts();
    var xs= getDec(rcc.c().name()).bs().stream().map(b->b.x().name()).toList();
    MSig imh= methodHeader(rcc,sig.m().get(),sig.rc()).get();
    ts= meet(Stream.concat(
      IntStream.range(0, imh.ts().size())
        .mapToObj(i->refine(xs,imh.ts().get(i),sig.ts().get(i).get())),
      Stream.of(refine(xs,imh.ret(),sig.ret().get()),ts)
      ).toList());
    rcc= rcc.withTs(ts);
    MSig improvedM= methodHeader(rcc,sig.m().get(),sig.rc()).get();
    var sigRes= sig.refine(improvedM.ts().stream().map(Optional::of).toList(),Optional.of(improvedM.ret()));
    impl= impl.map(i->i.withE(meet(i.e(),sigRes.ret().get())));
    var mRes= new inferenceGrammar.M(sigRes,impl);
    return new TSM(rcc.c().ts(),mRes);
    //TODO: Big mistake. We need to instead turn the lambda into a new anon typed literal when
    //we remove all the ?? from the head. Or do we?
    //what if some ? survives anyway?
    //if the C[Ts] becomes a value, export to class table
    //Also, if lambda in receiver position, export to class table immediately (or even before steps?)
    //Option: 
    // 1- make the inference only start from the original top methods
    // 2- add a name to all of the literals, export them to the table
    // 3- when a name is reached in the expression inference, it must be that was not top!!
    // (we could even keep the literal body in both positions)
    //Thus, the literal is never there, and all is typed literal.
    //{...} --> FreshName[FTV]:?{..}:IT
    //so we remove the 'Typed E', and..
    //the 'this' now will use the FreshName
    //TODO: make the long g into a proper mutable object, and then the labeller will be the stepStar method (only)
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

  ∀ i∈0..k Xs ⊢ Ti=T'i  : Tsi 
--------------------------------------------------(propagateXs)
  X1..Xn ⊢ C[T1..Tk]=C[T'1..T'k] : ?1..?n⊓Ts1⊓..⊓Tsk  //the first ?s are needed if n==0

--------------------------------------------------(propagateXs?)
  X1..Xn ⊢ C[Ts]=? : ?1..?n

--------------------------------------------------(propagateXsErr)
  X1..Xn ⊢ C[Ts]=Err : ?1..?n

  either C != C' or size(Ts) != size(Ts')   
--------------------------------------------------(propagateXsDiff)
  X1..Xn ⊢ C[Ts]=C'[Ts'] : ?1..?n

    
//On the (not) need of alpha: if no need of alpha in methSig (since two universes)
//then the X1..Xk is still not alphaed, thus is still the same of what methSig can give us here?
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
  Γ0 ⊢ e0.m[Ts](e1..en):T ==> Γ(n+1) ⊢ e'0.m[Ts](e'1..e'n):T

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

  M  = m[Xs](x1:T1 .. xn:Tn):_ { return e; }
  Γ, this:C[Ts],x1:T1 .. xn:Tn⊢ e ==>* Γ',this:_,x1:T'1 .. xn:T'n ⊢ e'
  T'0 = typeOf(e')
  interface C[Xs'] { _ m[Xs](_:IT1 .. _:ITn):IT0 _ } in Ds
  forall i in 0..n Xs' |- ITi=T'i : Tsi
  Ts' = Ts⊓Ts0⊓..⊓Tsn
  methodHeader(C[Ts'],m) = m[Xs](_:T"1.._:T"n):T"0
  M' = m[Xs](x1:T'1⊓T"1 .. xn:T'n⊓T"n):T'0⊓T"0 { return e'⊓T"0; }
------------------------------------------------------------------ (meth)
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
*/