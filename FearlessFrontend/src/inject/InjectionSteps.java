package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import inference.E;
import inference.Gamma;
import inference.IT;
import inferenceCore.Declaration;
import inferenceCore.M;
import pkgmerge.OtherPackages;
import utils.Bug;
import utils.OneOr;
import utils.Push;

public record InjectionSteps(Methods meths,OtherPackages other){
  public static List<Declaration> steps(Methods meths, List<Declaration> in, OtherPackages other){
    var s= new InjectionSteps(meths,other);
    //meths.cache().size will grow during iteration
    int size= meths.cache().size();
    var es= new ArrayList<Declaration>(meths.cache().values());//is linkedMashMap, so order is preserved
    List<Declaration> res= new ArrayList<>();
    for (int i= 0; i < size; i += 1){ res.add(stepDec(s, es.get(i))); }    
    return res;
  }
  private static Declaration stepDec(InjectionSteps s, Declaration di){
    var ms= di.ms().stream().map(m->{
      if (m.e().isEmpty()){ return m; }
      var e= m.e().get();
      List<IT> thisTypeTs= di.bs().stream().<IT>map(b->new IT.X(b.x())).toList();
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
      if (oe == e && !g.changed(s)){ e.sign(g); return e; }
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

  Declaration getDec(TName name){ return meths.from(name); }
  
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
    Optional<M> readOne= OneOr.opt("not well formed ms",ms.stream().filter(m->m.sig().rc()==RC.read));
    if (rc== RC.read){ return readOne; }
    if (rc== RC.mut){ return OneOr.opt("not well formed ms",ms.stream().filter(m->m.sig().rc()==RC.mut)); }
    assert rc== RC.imm;
    return OneOr.opt("not well formed ms",ms.stream()
      .filter(m->m.sig().rc()==RC.imm)).or(()->readOne);
  }
  public interface InstanceData<R>{ R apply(IT.RCC rcc, Declaration d, M m); }
  private <R> Optional<R> methodHeaderAnd(IT.RCC rcc,MName name,Optional<RC> favorite,InstanceData<R> f){
    var d= getDec(rcc.c().name());
    Stream<M> ms= d.ms().stream().filter(m->m.sig().m().equals(name));
    Optional<M> om= favorite//ms is used only one time: we use .map (returning Optional<Optional<M>>) not .flatMap 
      .map(rc->oneFromExplicitRC(ms.filter(mi->mi.sig().rc().equals(rc)).toList()))
      .orElseGet(()->oneFromGuessRC(ms.toList(),overloadNorm(rcc.rc())));
    if (om.isEmpty()){ 
    return Optional.empty(); }
    return Optional.of(f.apply(rcc,d,om.get()));
  }
  private MSig methodHeaderInstance(IT.RCC rcc,Declaration d,M m){
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
  //-----------Metarules
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
  private E nextL(Gamma g, E.Literal l){
    var selfPrecise= preciseSelf(l); 
    if (l.rc().isPresent() && l.t() instanceof IT.U){ l = l.withT(preferred(selfPrecise.get())); }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    if (!l.infA()){ assert l.cs().isEmpty(); l= meths.expandLiteral(l,rcc.c()); }
    var s= g.snapshot();
    boolean same= true;
    var res= new ArrayList<inference.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    for (var mi: l.ms()){
      if (mi.impl().isEmpty()){ res.add(mi); continue; }//we are also keeping methods from supertypes, and not all will be in need of implementation
      TSM next= nextMStar(g,l.thisName(),meths.cache().containsKey(l.name()),selfPrecise,rcc,ts,mi);
      same &= 
        next.m.sig().equals(mi.sig())
        && next.m.impl().get().e() == mi.impl().get().e() 
        && next.ts.equals(ts);
      res.add(next.m);
      ts = next.ts;
    }
    if (same && !g.changed(s)){ return commitToTable(l,rcc); }
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
  record TSM(List<IT> ts, inference.M m){}
  private TSM nextMStar(Gamma g, String thisN, boolean committed, Optional<IT.RCC> selfPrecise, IT.RCC rcc, List<IT> ts, inference.M m){
    assert selfPrecise.isEmpty() || rcc.isTV();
    assert m.impl().isPresent();
    rcc = rcc.withTs(ts);
    IT selfT= selfPrecise.<IT>map(it->it).orElse(IT.U.Instance);
    MName mName= m.sig().m().get();
    var size= mName.arity();
    var xs= m.impl().get().xs();
    var args= m.sig().ts();
    g.newScope();
    g.declare(thisN, selfT);
    for(int i= 0; i < size; i += 1){ g.declare(xs.get(i), args.get(i).get()); }
    E e= nextStar(g,m.impl().get().e());
    args= xs.stream().map(x->Optional.of(g.get(x))).toList(); 
    g.popScope();
    if (committed){
      var mRes= new inference.M(m.sig(),Optional.of(m.impl().get().withE(e)));
      return new TSM(rcc.c().ts(),mRes);
    }
    var improvedSig= m.sig().withTsT(args, e.t());
    var ret= improvedSig.ret().get();
    ts= rcc.c().ts();
    var sigTs= improvedSig.ts();
    //Note: imh has the Xs in place, both type and meth. No rename needed
    var omh= methodHeaderAnd(rcc,mName,improvedSig.rc(),(_,_,mi)->mi);
    if (omh.isEmpty()){
      var impl= m.impl().get().withE(meet(e,ret));
      var mRes= new inference.M(improvedSig,Optional.of(impl));
      return new TSM(ts,mRes);
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
    assert improvedM.bs.equals(improvedSig.bs().get().stream().map(b->b.x()).toList()):
      ""+methodHeader(rcc,mName,improvedSig.rc())+improvedM.bs+ " "+improvedSig.bs().get(); 
    var sigRes= improvedSig.withTsT(improvedM.ts().stream().map(Optional::of).toList(),improvedM.ret());
    e = meet(e,sigRes.ret().get());
    var mRes= new inference.M(sigRes,Optional.of(m.impl().get().withE(e)));
    return new TSM(rcc.c().ts(),mRes);
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