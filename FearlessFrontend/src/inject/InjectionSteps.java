package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.Sig;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import inference.E;
import inference.Gamma;
import inference.IT;
import utils.Bug;
import utils.OneOr;
import utils.Push;

public record InjectionSteps(Methods meths){
  public static List<core.E.Literal> steps(Methods meths, List<inference.E.Literal> tops){
    var s= new InjectionSteps(meths);
    List<core.E.Literal> res= new ArrayList<>();
    for (var l:tops){
      assert l.thisName().equals("this");
      res.add(stepDec(s,meths.cache().get(l.name()), l));
    }
    return List.copyOf(res);
  }
  private static core.E.Literal stepDec(InjectionSteps s, core.E.Literal di, inference.E.Literal li){
    List<core.M> ms= li.ms().stream().map(m->stepDecM(s,di,m)).toList();
    return di.withMs(ms);
  }
  private static boolean sameM(core.Sig s1, inference.M.Sig s2){
    return s1.m().equals(s2.m().get()) && s1.rc().equals(s2.rc().orElse(RC.imm));
  }
  private static core.M stepDecM(InjectionSteps s, core.E.Literal di, inference.M m){
    core.M mCore= utils.OneOr.of("Method mismatch",di.ms().stream().filter(mi->sameM(mi.sig(),m.sig())));
    if (m.impl().isEmpty()){ return mCore; }//assert same type as m lifted to core
    inference.E e= m.impl().get().e();
    List<IT> thisTypeTs= di.bs().stream().<IT>map(b->new IT.X(b.x())).toList();
    List<String> xs= m.impl().get().xs();
    var thisType= new IT.RCC(mCore.sig().rc(),new IT.C(di.name(),thisTypeTs));
    inference.E ei= meet(e,TypeRename.tToIT(mCore.sig().ret()));
    Gamma g= Gamma.of(xs,TypeRename.tToIT(mCore.sig().ts()),di.thisName(),thisType);
    ei= s.nextStar(g, ei);
    return new core.M(mCore.sig(),xs,Optional.of(new ToCore().of(ei)));
  }
  static E meet(E e, IT t){ return e.withT(meet(e.t(),t)); }
  static IT meet(IT t1, IT t2){ 
    if (t2 == IT.U.Instance){ return t1; }
    if (t1 == IT.U.Instance){ return t2; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.rc().equals(x2.rc())){ 
        return IT.Err.Instance; }
      if (!x1.c().name().equals(x2.c().name())){
        return IT.Err.Instance; }
      assert x1.c().ts().size() == x2.c().ts().size();
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
  E nextStar(Gamma g, E e){
    if (e.done(g)){ return e; }
    while (true){
      var s= g.snapshot();
      var oe= next(g,e);
      //assert oe == e || g.changed(s) || !oe.equals(e) : "Allocated equal E: "+e.getClass()+"\n"+e;
      if (oe == e && !g.changed(s)){ e.sign(g); return e; }
      //if (oe.equals(e) && !g.changed(s)){ e.sign(g); return e; }//this line is useful for debugging when == gets buggy
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
    var s= g.snapshot();
    boolean same= true;
    var res= new ArrayList<E>(es.size());
    for (E ei:es){
      E next= nextStar(g,ei);
      same &= next == ei;
      res.add(next);
    }
    if (same && !g.changed(s)){ return es; }
    return Collections.unmodifiableList(res);
  }
  E next(Gamma g, E e){ return switch (e){
    case E.X x -> nextX(g,x);
    case E.Literal l -> nextL(g,l);
    case E.Call c -> nextC(g,c);
    case E.ICall c -> nextIC(g,c);
    case E.Type c -> nextT(g,c);
  };}

  core.E.Literal getDec(TName name){ return meths.from(name); }
  
  private IT preferred(IT.RCC type){
    var d= getDec(type.c().name());
    assert d != null : type;
    var cs= d.cs().stream().filter(c->c.name().s().equals("base.WidenTo")).toList();
    if (cs.size() == 0){ return type; } 
    assert cs.size() == 1;
    assert cs.getFirst().ts().size() == 1;
    var dom= d.bs().stream().map(b->b.x()).toList();
    IT wid= TypeRename.of(TypeRename.tToIT(cs.getFirst().ts().getFirst()), dom, type.c().ts());
    return wid;
  }
  private RC overloadNorm(RC rc){ return switch(rc){
    case imm->RC.imm;
    case iso->RC.mut;
    case mut->RC.mut;
    case mutH->RC.mut;
    case read->RC.read;    
    case readH->RC.read;
  };}
  private Optional<core.M> oneFromExplicitRC(List<core.M> ms){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    assert ms.isEmpty():"Ambiguous method header for explicit RC";
    return Optional.empty();
  }  
  private Optional<core.M> oneFromGuessRC(List<core.M> ms, RC rc){
    Optional<core.M> readOne= OneOr.opt("not well formed ms",ms.stream().filter(m->m.sig().rc()==RC.read));
    if (rc== RC.read){ return readOne; }
    if (rc== RC.mut){ return OneOr.opt("not well formed ms",ms.stream().filter(m->m.sig().rc()==RC.mut)); }
    assert rc== RC.imm;
    return OneOr.opt("not well formed ms",ms.stream()
      .filter(m->m.sig().rc()==RC.imm)).or(()->readOne);
  }
  public interface InstanceData<R>{ R apply(IT.RCC rcc, core.E.Literal d, core.M m); }
  private <R> Optional<R> methodHeaderAnd(IT.RCC rcc, MName name, Optional<RC> favorite, InstanceData<R> f){
    var d= getDec(rcc.c().name());
    Stream<core.M> ms= d.ms().stream().filter(m->m.sig().m().equals(name));
    Optional<core.M> om= favorite.isPresent()
      ? oneFromExplicitRC(ms.filter(mi -> mi.sig().rc().equals(favorite.get())).toList())
      : oneFromGuessRC(ms.toList(), overloadNorm(rcc.rc()));
    //Optional<M> om= favorite//had to replace this perfectly reasonable code with the above because all AIs could not understand it. 
    //  .map(rc->oneFromExplicitRC(ms.filter(mi->mi.sig().rc().equals(rc)).toList()))
    //  .orElseGet(()->oneFromGuessRC(ms.toList(),overloadNorm(rcc.rc())));
    if (om.isEmpty()){ return Optional.empty(); }
    return Optional.of(f.apply(rcc,d,om.get()));
  }
  private MSig methodHeaderInstance(IT.RCC rcc,core.E.Literal d,core.M m){
    List<String> xs= d.bs().stream().map(b->b.x()).toList();
    assert xs.stream().distinct().count() == xs.size();
    List<String> bs= m.sig().bs().stream().map(b->b.x()).toList();
    var ts= rcc.c().ts();
    List<IT> tsRes= m.sig().ts().stream()
      .map(t->TypeRename.of(TypeRename.tToIT(t),xs,ts))
      .toList();
    IT tRet= TypeRename.of(TypeRename.tToIT(m.sig().ret()),xs,ts);
    return new MSig(m.sig().rc(),bs,tsRes,tRet);
  }
  private Optional<MSig> methodHeader(IT.RCC rcc,MName name,Optional<RC> favorite){
    return methodHeaderAnd(rcc,name,favorite,this::methodHeaderInstance);
  }
  private static List<IT> _qMarks(int n){ return IntStream.range(0, n).<IT>mapToObj(_->IT.U.Instance).toList(); }
  static List<List<IT>> smallQMarks=IntStream.range(0, 100)
    .mapToObj(i->_qMarks(i)).toList();//Safe: Stream.toList returns an unmodifiable list; and it is used also in _qMarks
  private List<IT> qMarks(int n){ return n < 100 ? smallQMarks.get(n): _qMarks(n); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i->i==n?t:IT.U.Instance).toList(); }
  
  private E nextX(Gamma g, E.X x){ 
    var t1= g.get(x.name());//TODO: this may repeat if entered back in the same scope? no if meth header properly updated?
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
    var e= nextStar(g,c.e());
    var es= nextStar(g,c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e,es); }
    Optional<MSig> om= methodHeader(rcc,c.name(),Optional.empty());
    if (om.isEmpty()){ return c.withEEs(e,es); }
    MSig m= om.get();
    List<IT> ts= qMarks(m.bs().size());
    var es1= IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i),TypeRename.of(m.ts().get(i),m.bs(),ts)))
      .toList();
    var t= meet(c.t(),TypeRename.of(m.ret(),m.bs(),ts));
    var call= new E.Call(e,c.name(),Optional.of(m.rc()),ts,es1,c.pos());
    return call.withT(t);
  }
  private E nextC(Gamma g, E.Call c){
    var e= nextStar(g,c.e());
    var es= nextStar(g, c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e,es); }
    Optional<MSig> om= methodHeader(rcc,c.name(),c.rc());
    if (om.isEmpty()){ return c.withEEs(e,es); }
    MSig m= om.get();
    RC rc= c.rc().orElse(m.rc());
    assert m.ts().size() == es.size();
    List<IT> targs= newTargs(c, es, m);
    var it= meet(c.t(),TypeRename.of(m.ret(),m.bs(),targs));
    var es1 = meet(es, m, targs);
    if (e == c.e() && es == c.es() && targs.equals(c.targs())  && it.equals(c.t())){ return c; } 
    return c.withMore(e,rc,targs,es1,it); 
  }
  private List<IT> newTargs(E.Call c, List<E> es, MSig m){
    if(m.bs().isEmpty()){ return List.of(); }
    assert c.targs().isEmpty() || c.targs().size() == m.bs().size();
    var a= IntStream.range(0, c.es().size())
      .mapToObj(i->refine(m.bs(),m.ts().get(i),es.get(i).t()));
    var r= Stream.of(refine(m.bs(),m.ret(),c.t()),c.targs());
    return meet(Stream.concat(a,r).toList());
  }
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    if (l.rc().isEmpty()){ return Optional.empty(); }
    var xs= l.bs().stream().<IT>map(b->new IT.X(b.x())).toList();
    return Optional.of(new IT.RCC(l.rc().get(),new IT.C(l.name(),xs)));
  }
  //------
  
  private E nextL(Gamma g, E.Literal l){
    if (!l.infA() && !l.cs().isEmpty()){ l = meths.expandDeclaration(l); }
    var selfPrecise= preciseSelf(l);
    if (l.rc().isPresent() && l.t() instanceof IT.U){ l = l.withT(preferred(selfPrecise.get())); }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    if (!l.infA()){ assert l.cs().isEmpty(); l = meths.expandLiteral(l,rcc.c()); }
    boolean changed= false;
    var res= new ArrayList<inference.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    for (var mi: l.ms()){
      if (mi.impl().isEmpty()){ res.add(mi); continue; }//we are also keeping methods from supertypes, and not all will be in need of implementation
      TSM next= nextMStar(g,l.thisName(),meths.cache().containsKey(l.name()),selfPrecise,rcc,ts,mi);
      changed |= next.m != mi || !next.ts.equals(ts);
      res.add(next.m);
      ts = next.ts;
    }
    if (!changed){ return commitToTable(l,rcc); }
    var ms= Collections.unmodifiableList(res);
    IT t= rcc.withTs(ts);
    return commitToTable(l.withMsT(ms,t),t);
  }
  private E commitToTable(E.Literal l, IT t){
    if (l.rc().isPresent() || !t.isTV() || !(t instanceof IT.RCC rcc) || hasU(l.ms())){ return l; }
    assert l.cs().isEmpty();
    var noMeth= l.ms().stream().allMatch(m->m.impl().isEmpty());
    if (noMeth){ return new E.Type(rcc,rcc,l.pos(), l.g()); }//TODO: what if it was not a fresh name but a user defined name?
    List<IT.C> cs= Push.of(rcc.c(),meths.fetchCs(rcc.c()));
    meths.checkMagicSupertypes(l.name(),cs);
    l = new E.Literal(Optional.of(rcc.rc()),l.name(),l.bs(),cs,l.thisName(),l.ms(), t, l.pos(), true, l.g());
    var resD= meths.injectDeclaration(l);
    meths.cache().put(resD.name(),resD);//can we simply remove dsMap and use meth cache all the time?
    return l;
  }
  private static boolean hasU(List<inference.M> ms){
    return !ms.stream().allMatch(m->
      m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t->t.get().isTV())
    );
  }
  private static List<Optional<IT>> updateArgs(List<String> xs, List<Optional<IT>> old, Gamma g){
    int n= xs.size();
    assert old.size() == n;
    boolean changed= false;
    ArrayList<Optional<IT>> out= new ArrayList<>(n);
    for(int i= 0; i < n; i++){
      var x= xs.get(i);
      var oi= old.get(i);
      if ("_".equals(x)){ out.add(oi); continue; }
      assert oi.isPresent();
      var ti= g.get(x);
      if (oi.get().equals(ti)){ out.add(oi); continue; }
      changed= true;
      out.add(Optional.of(ti));
    }
    return changed ? Collections.unmodifiableList(out) : old;
  }
  record TSM(List<IT> ts, inference.M m){}
  private TSM nextMStar(Gamma g, String thisN, boolean committed, Optional<IT.RCC> selfPrecise, IT.RCC rcc, List<IT> ts, inference.M m){
    assert selfPrecise.isEmpty() || rcc.isTV();
    assert m.impl().isPresent();
    var sig0= m.sig();
    var impl0= m.impl().get();
    rcc = rcc.withTs(ts);
    IT selfT= selfPrecise.<IT>map(it->it).orElse(IT.U.Instance);
    MName mName= sig0.m().get();
    var size= mName.arity();
    var xs= impl0.xs();
    var args= sig0.ts();
    g.newScope();
    g.declare(thisN, selfT);
    for(int i= 0; i < size; i += 1){ g.declare(xs.get(i), args.get(i).get()); }
    E e= nextStar(g,impl0.e());
    args= updateArgs(xs,args, g);
    g.popScope();
    if (committed){
      if (e == impl0.e()){ return new TSM(ts,m); }
      return new TSM(ts,new inference.M(sig0,Optional.of(impl0.withE(e))));
    }
    var improvedSig= sig0.withTsT(args,e.t());
    var ret= improvedSig.ret().get();
    ts= rcc.c().ts();
    var sigTs= improvedSig.ts();
    //Note: imh has the Xs in place, both type and meth. No rename needed
    var omh= methodHeaderAnd(rcc,mName,improvedSig.rc(),(_,_,mi)->mi);
    if (omh.isEmpty()){
      var impl= impl0.withE(meet(e,ret));
      if (improvedSig == sig0 && impl == impl0){ return new TSM(ts,m); }
      return new TSM(ts,new inference.M(improvedSig,Optional.of(impl)));
    }    
    var Xs= getDec(rcc.c().name()).bs().stream().map(b->b.x()).toList();
    var imh= omh.get().sig();
    ts= meet(Stream.concat(
      IntStream.range(0, imh.ts().size())
        .mapToObj(i->refine(Xs,TypeRename.tToIT(imh.ts().get(i)),sigTs.get(i).get())),
      Stream.of(refine(Xs,TypeRename.tToIT(imh.ret()),ret),ts)
      ).toList());
    rcc= rcc.withTs(ts);
    MSig improvedM= methodHeader(rcc,mName,improvedSig.rc()).get();
    improvedM = TypeRename.normalizeHeaderBs(improvedM, improvedSig);
    //Overall we should apply normalizeHeaderBs only if selfPrecise is absent; otherwise assert that the Xs are the righ ones
    assert improvedM.bs().equals(improvedSig.bs().get().stream().map(b->b.x()).toList()):
      ""+methodHeader(rcc,mName,improvedSig.rc())+improvedM.bs()+ " "+improvedSig.bs().get(); 
    var sigRes= improvedSig.withTsT(improvedM.ts().stream().map(Optional::of).toList(),improvedM.ret());
    e = meet(e,sigRes.ret().get());
    var impl= impl0.withE(e);
    if (sigRes == sig0 && impl == impl0){ return new TSM(rcc.c().ts(),m); }
    return new TSM(rcc.c().ts(),new inference.M(sigRes,Optional.of(impl)));
  }
  List<IT> refine(List<String> xs,IT t, IT t1){
    if( t1 instanceof IT.U){ return qMarks(xs.size()); } 
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
    if (i == -1){ return qMarks(xs.size()); }
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
}
record MSig(RC rc, List<String> bs, List<IT> ts, IT ret){}