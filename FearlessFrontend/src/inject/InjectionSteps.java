package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.MName;
import core.RC;
import core.TName;
import core.TSpan;
import inference.E;
import inference.Gamma;
import inference.IT;
import inference.IT.RCC;
import inference.M;
import message.WellFormednessErrors;
import utils.Bug;
import utils.OneOr;
import utils.Push;
import utils.Streams;
/**
Inference fix-point core loop relies on identity for E.
Core loop relies on `oe == e` to detect stabilization in O(1) and avoid a deep
`equals(e)` walk each iteration:
`if (oe == e && !g.changed(s)){ e.sign(g); return e; }`
Any rewrite of terms containing Es MUST return the original
instance (==) if no structural change is performed.

Exact identity-sensitive set
(must preserve == on no-op updates, including inside Optional/List/Map containers):
- inference.E.X
- inference.E.Type
- inference.E.Call
- inference.E.ICall
- inference.E.Literal
- inference.M
- inference.M.Impl
Any other form of allocation prevention is just premature optimization
and should be simplified away.
Only preserve identity (==) for E/M (and their deciding containers like List<E>/List<M>/Optional<M.Impl>).
For IT/Sig/TName (and List<IT>/List<Optional<IT>> etc.) NEVER do "same -> return old": allocate freely.

Non-identity-sensitive (allocation/equal ok): types (IT), signatures (Sig), names (TName),
and other data that cannot contain E.

Offensive style: Optional.get() is intentional where invariants guarantee presence;
absence indicates a bug and should crash.
*/


public record InjectionSteps(Methods meths){
  public static List<core.E.Literal> steps(Methods meths, List<inference.E.Literal> tops){
    var s= new InjectionSteps(meths);
    assert tops.stream().allMatch(l->l.thisName().equals("this"));
    return tops.stream()
      .map(l->s.stepDec(meths.cache().get(l.name()), l)).toList();
  }
  private core.E.Literal stepDec(core.E.Literal di, inference.E.Literal li){
    List<core.M> ms= li.ms().stream().map(m -> stepDecM(di, m)).toList();
    return di.withMs(ms);
  }
  private boolean sameM(core.Sig s1, inference.M.Sig s2){
    return s1.m().equals(s2.m().get()) && s1.rc().equals(s2.rc().orElse(RC.imm));
  }
  private core.M stepDecM(core.E.Literal di, inference.M m){
    core.M mCore= utils.OneOr.of("Method mismatch", di.ms().stream().filter(mi -> sameM(mi.sig(), m.sig())));
    if (m.impl().isEmpty()){ return mCore; }//assert same type as m lifted to core
    inference.E e= m.impl().get().e();
    TSpan span= di.name().approxSpan();
    List<IT> thisTypeTs= di.bs().stream().<IT>map(b -> new IT.X(b.x(),span)).toList();
    List<String> xs= m.impl().get().xs();
    var thisType= new IT.RCC(mCore.sig().rc(), new IT.C(di.name(), thisTypeTs),span);//no preferred on self names
    inference.E ei= meet(e, TypeRename.tToIT(mCore.sig().ret()));
    Gamma g= Gamma.of(xs, TypeRename.tToIT(mCore.sig().ts()), di.thisName(), thisType);
    ei = nextStar(Push.of(di.bs(), m.sig().bs().get()), g, ei);
    return new core.M(mCore.sig(), xs, Optional.of(new ToCore().of(ei, m.impl().get().e())));
  }
  E meet(E e, IT t){
    e = prototypeAscribeRootReceiver(e, t);
    return e.withT(meetKeepLeft(e.t(), t));
  }
  IT meetKeepLeft(IT l, IT r){
    if (r == IT.U.Instance){ return l; }
    if (l == IT.U.Instance){ return r; }
    if (l instanceof IT.Err){ return meet(l,r); }
    if (r instanceof IT.Err){ return l; }
    if (l instanceof IT.RCC a && r instanceof IT.RCC b){
      if (!a.c().name().equals(b.c().name())){
        var va= viewAs(a, b.c().name());
        if (va.isPresent()){ return meetKeepLeft(va.get(), b); }
        return leastBad(a,b);
      }
      return a.withRCTs(a.rc(), meetKeepLeft(a.c().ts(), b.c().ts()));
    }
    if (!(l instanceof IT.RCX a && r instanceof IT.RCX b)){ return l; }
    if (!a.x().equals(b.x())){ return l; }
    return a;
  }
  private static IT leastBad(RCC a, RCC b){ return a.badness() <= b.badness() ? a : b;  }
  static IT meet(IT t1, IT t2){
    if (t2 == IT.U.Instance){ return t1; }
    if (t1 == IT.U.Instance){ return t2; }
    if (t1.equals(t2)){ return t1; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.c().name().equals(x2.c().name())){ return leastBad(x1,x2); }//return IT.Err.merge(t1,t2); }
      RC rc= meetRcNoH(x1.rc(), x2.rc());
      return x1.withRCTs(rc,meet(x1.c().ts(), x2.c().ts()));
    }
    if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX x2)){ return IT.Err.merge(t1,t2); }
    if (!x1.x().equals(x2.x())){ return IT.Err.merge(t1,t2); }
    return x1.withRC(meetRcNoH(x1.rc(), x2.rc()));
  }
  static RC meetRcNoH(RC a, RC b){
    if (a == b){ return noH(a); }
    if (a == RC.iso){ return noH(b); }
    if (b == RC.iso){ return noH(a); }
    return RC.read;
  }
  static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
  static List<IT> meet(List<IT> t1, List<IT> t2){
    assert t1.size() == t2.size() : "should have gone in Err before";
    return IntStream.range(0, t1.size()).mapToObj(i -> meet(t1.get(i), t2.get(i))).toList();
  }
  List<IT> meetKeepLeft(List<IT> l, List<IT> r){ return norm(l,Streams.zip(l, r).map((li,ri)->meetKeepLeft(li, ri)).toList()); }
  List<IT> meetKeepLeft(List<List<IT>> tss){
    int size= tss.getFirst().size();
    assert tss.stream().allMatch(ts -> ts.size() == size);
    return IntStream.range(0,size)
    .mapToObj(i-> tss.stream()
      .map(ts->ts.get(i))
      .reduce((a,b)->meetKeepLeft(a,b))
      .orElseThrow())
    .toList();
  }
  E nextStar(List<B> bs, Gamma g, E e){
    if (e.done(g)){ return e; }
    while (true){
      var s= g.snapshot();
      var oe= next(bs, g, e);
      assert oe == e || g.changed(s) || !oe.equals(e) : "Allocated equal E:"+e.getClass()+"\n"+e;//TODO: very heavy assertion
      if (oe == e && !g.changed(s)){ e.sign(g); return e; }
      //if (oe.equals(e) && !g.changed(s)){ e.sign(g); return e; }//this line is useful for debugging when == gets buggy
      e = oe;
    }
  }
  private List<M> fixArity(List<M> ms, TName name, TName newName){
    if (name.equals(newName)){ return ms; }
    return norm(ms,ms.stream().map(mi->fixArity(mi, name, newName)).toList());
  }
  private List<E> nextStar(List<B> bs, Gamma g, List<E> es){
    return norm(es,es.stream().map(ei->nextStar(bs, g, ei)).toList());
  }
  private List<E> meet(List<E> es, MSigL m, List<IT> targs){
    return norm(es,IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i), m.p(i,targs))).toList());
  }
  E next(List<B> bs, Gamma g, E e){
    try{ return _next(bs,g,e); }
    catch(WellFormednessErrors.ErrToFetchContext depthErr){
      throw meths.p().err().itTooDeep(e,depthErr.c);
  }}
  E _next(List<B> bs, Gamma g, E e){ return switch (e){
    case E.X x -> nextX(bs, g, x);
    case E.Literal l -> nextL(bs, g, l);
    case E.Call c -> nextC(bs, g, c);
    case E.ICall c -> nextIC(bs, g, c);
    case E.Type c -> nextT(bs, g, c);
  };}
  core.E.Literal getDec(TName name){ return meths.from(name); }
  private IT preferred(IT.RCC type){
    var d= meths._from(type.c().name());
    if (d == null){ return type; }//This can happen for {..}.foo
    assert d != null : type;
    var cs= d.cs().stream().filter(c -> c.name().s().equals("base.WidenTo")).toList();
    if (cs.isEmpty()){ return type; }
    assert cs.size() == 1;
    assert cs.getFirst().ts().size() == 1;
    var dom= d.bs().stream().map(b -> b.x()).toList();
    IT wid= TypeRename.of(TypeRename.tToIT(cs.getFirst().ts().getFirst()), dom, type.c().ts());
    var w=(IT.RCC)wid;//TODO: this must be made to fail in a test, then we need to improve the well formedness error of WidenTo
    return new IT.RCC(type.rc(), w.c(),type.span());
  }
  private RC overloadNorm(RC rc){ return switch (rc){
    case imm -> RC.imm;
    case iso -> RC.mut;
    case mut -> RC.mut;
    case mutH -> RC.mut;
    case read -> RC.read;
    case readH -> RC.read;
  };}
  private Optional<core.M> oneFromExplicitRC(List<core.M> ms){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    assert ms.isEmpty() : "Ambiguous method header for explicit RC";
    return Optional.empty();
  }
  private Optional<core.M> oneFromGuessRC(List<core.M> ms, RC rc){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    Optional<core.M> readOne= OneOr.opt("not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.read));
    Optional<core.M> mutOne= OneOr.opt("not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.mut));
    Optional<core.M> immOne= OneOr.opt("not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.imm));
    if (rc == RC.read){ return readOne.or(() -> immOne).or(() -> mutOne); }
    if (rc == RC.mut){ return mutOne.or(() -> readOne).or(()->immOne); }
    assert rc == RC.imm;
    return immOne.or(() -> readOne).or(()->mutOne);
  }
  public interface InstanceData<R> { R apply(IT.RCC rcc, core.E.Literal d, core.M m); }
  private <R> Optional<R> methodHeaderAnd(IT.RCC rcc, MName name, Optional<RC> favorite, InstanceData<R> f){
    var d= meths._from(rcc.c().name());
    if (d == null){ return Optional.empty(); }//case {..}.foo
    Stream<core.M> ms= d.ms().stream().filter(m -> m.sig().m().equals(name));
    Optional<core.M> om= favorite.isPresent()
        ? oneFromExplicitRC(ms.filter(mi -> mi.sig().rc().equals(favorite.get())).toList())
        : oneFromGuessRC(ms.toList(), overloadNorm(rcc.rc()));
    return om.map(mm->f.apply(rcc, d, mm));
  }
  private MSigL methodHeaderInstance(IT.RCC rcc, core.E.Literal d, core.M m){
    List<String> clsXs= d.bs().stream().map(b->b.x()).toList();
    assert clsXs.stream().distinct().count() == clsXs.size();
    List<String> methXs= m.sig().bs().stream().map(b->b.x()).toList();
    assert methXs.stream().distinct().count() == methXs.size();
    assert Collections.disjoint(clsXs, methXs);
    var clsArgs= rcc.c().ts();
    assert clsArgs.size() == clsXs.size();
    List<String> xs= Push.of(clsXs,methXs);//TODO: could avoid materializing the two lists
    List<IT> ps0= m.sig().ts().stream().map(TypeRename::tToIT).toList();
    IT ret0= TypeRename.tToIT(m.sig().ret());
    return new MSigL(m.sig().rc(), xs, clsArgs, ps0, ret0);
  }
  private Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){
    return methodHeaderAnd(rcc, name, favorite, this::methodHeaderInstance);
  }
  private static List<IT> _qMarks(int n){
    return IntStream.range(0, n).<IT>mapToObj(_ -> IT.U.Instance).toList();
  }
  static List<List<IT>> smallQMarks= IntStream.range(0, 100).mapToObj(i -> _qMarks(i)).toList();// Safe: Stream.toList
  private List<IT> qMarks(int n){ return n < 100 ? smallQMarks.get(n) : _qMarks(n); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i -> i == n ? t : IT.U.Instance).toList(); }
  private E nextX(List<B> bs, Gamma g, E.X x){
    var t1= g.get(x.name());//TODO: this may repeat if entered back in the same scope? no if meth header properly updated?
    var t2= x.t();
    if (t1.equals(t2)){ return x; }
    var t3= meetKeepLeft(t1, t2);
    if (t3 instanceof IT.Err){ return x; }
    g.update(x.name(), t3);
    return x.withT(t3);
  }
  private E nextT(List<B> bs, Gamma g, E.Type t){
    var t1= preferred(t.type());
    var t2= t.t();
    if (t1.equals(t2)){ return t; }
    var t3= meetKeepLeft(t1, t2);
    return t.withT(t3);
  }
  private E nextIC(List<B> bs, Gamma g, E.ICall c){
    var e= nextStar(bs, g, c.e());
    var es= nextStar(bs, g, c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, es); }
    Optional<MSigL> om= methodHeader(rcc, c.name(), Optional.empty());
    if (om.isEmpty()){ return c.withEEs(e, es); }
    MSigL m= om.get();
    List<IT> ts= qMarks(m.bsArity());
    var es1= IntStream.range(0, es.size())
      .mapToObj(i->meet(es.get(i), m.p(i,ts)))
      .toList();
    var t= meetKeepLeft(c.t(), m.ret(ts));
    var call= new E.Call(e, c.name(), Optional.of(m.rc()), ts, es1, c.src());
    return call.withT(t);
  }
  private E nextC(List<B> bs, Gamma g, E.Call c){
    var e= nextStar(bs, g, c.e());
    var es= nextStar(bs, g, c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, es); }
    Optional<MSigL> om= methodHeader(rcc, c.name(), c.rc());
    if (om.isEmpty()){ return c.withEEs(e, es); }
    MSigL m= om.get();
    RC rc= c.rc().orElse(m.rc());
    assert m.arity() == es.size();
    List<IT> all= newAllTs(c, es, m);
    assert all.size() == m.nCls()+m.bsArity()
      : "Call targs arity mismatch for "+c.name()
      +": got "+all.size()+" expected "+(m.nCls()+m.bsArity())
      +" (nCls="+m.nCls()+" bs="+m.bsArity()+")";
    List<IT> clsTs= all.subList(0, m.nCls());
    List<IT> targs= all.subList(m.nCls(), all.size());
    e = meet(e, rcc.withTs(clsTs));
    m= m.withClsArgs(clsTs);
    var it= meet(c.t(), m.ret(targs));
    var es1= meet(es, m, targs);
    if (e == c.e() && es1 == c.es() && targs.equals(c.targs()) && it.equals(c.t())){ return c; }
    return c.withMore(e, rc, targs, es1, it);
  }
  private List<IT> newAllTs(E.Call c, List<E> es, MSigL m){
    List<IT> base= Push.of(m.clsArgs(), MSigL.fixTargs(c.targs(), m.bsArity()));
    if (m.bsArity() + m.clsArgs().size() == 0){ return List.of(); }//this is just an optimization
    Stream<List<IT>> a= IntStream.range(0, es.size())
      .mapToObj(i -> refine(m.xs(), m.ps0().get(i), es.get(i).t()));
    List<IT> r= refine(m.xs(), m.ret0(), c.t());
    List<List<IT>> tss= Stream.of(
      Stream.of(base),
      a,
      Stream.of(r)).flatMap(s->s).toList();
    return meetKeepLeft(tss);
  }
  private Optional<IT.RCC> precisePublicSelf(E.Literal l){
    if (l.infName()){ return superSelf(l); }
    var xs= l.bs().stream().<IT>map(b -> new IT.X(b.x(),l.name().approxSpan())).toList();
    var fav= needMutRcFromMethods(l.ms())?RC.mut:RC.imm;
    return Optional.of(new IT.RCC(l.rc().orElse(fav), new IT.C(l.name(), xs),l.name().approxSpan()));
  }
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    if (l.infName() && l.rc().isEmpty()){ return Optional.empty(); }
    var xs= l.bs().stream().<IT>map(b -> new IT.X(b.x(),l.name().approxSpan())).toList();
    var fav= needMutRcFromMethods(l.ms())?RC.mut:RC.imm;
    return Optional.of(new IT.RCC(l.rc().orElse(fav), new IT.C(l.name(), xs),l.name().approxSpan()));
  }
  private Optional<IT.RCC> superSelf(E.Literal l){
    if (l.cs().size() != 1){ return preciseSelf(l); }
    if (l.infName() && l.rc().isEmpty()){ return Optional.empty(); }
    var fav= needMutRcFromMethods(l.ms())?RC.mut:RC.imm;
    return Optional.of(new IT.RCC(l.rc().orElse(fav), l.cs().getFirst(),l.name().approxSpan()));
  }
  static boolean needMutRcFromMethods(List<inference.M> ms){ return ms.stream().anyMatch(m -> m.sig().rc()==Optional.of(RC.mut)); }
  TSM nextMStar(List<B> bs,Gamma g,String thisN,boolean committed,Optional<IT.RCC> selfPrecise,IT.RCC rcc,inference.M m){
    return m.impl().isEmpty()
      ? nextMStarAbs(committed,rcc, m)
      : nextMStarOp(bs, g, thisN, committed, selfPrecise, rcc, m);
    }
  private E nextL(List<B> bs, Gamma g, E.Literal l){
    var infHead= l.infHead();//infHead is set in l.withCsMs and l.withMs and l.withMsT
    // to mean the HEAD is inferred as IT.RCC and has already been used to expand methods
    var selfPub= precisePublicSelf(l);
    var selfPrecise= preciseSelf(l);
    var selfSuper= superSelf(l);
    if (!infHead){
      if (!l.infName()){ l = l.withT(preferred(selfPub.get())); }
      else if (selfSuper.isPresent()){ l = l.withT(preferred(selfSuper.get())); }
      if (!(l.t() instanceof IT.RCC rcc)){ return l; }//!infHead after passing this test means right now we can expand methods
      if (!l.infName()){ l = meths.expandDeclaration(l,true); }
      else { l = meths.expandLiteral(l, rcc.c()); }
      if (needMutRcFromMethods(l.ms())){ l = l.withT(new IT.RCC(RC.mut, rcc.c(), rcc.span())); }
    }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    boolean changed= false;
    var res= new ArrayList<inference.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    for (var mi : l.ms()){
      if (mi.impl().isPresent()){ assert selfPrecise.isEmpty() || rcc.isTV(); }
      TSM next= nextMStar(bs, g, l.thisName(), meths.cache().containsKey(l.name()), selfPrecise, rcc.withTs(ts), mi);
      assert next.m == mi || !next.m.equals(mi) : "Allocated equal M:\n"+mi;
      var ts1= meetKeepLeft(ts, next.ts);
      changed |= next.m != mi || !ts1.equals(ts);
      res.add(next.m);
      ts = ts1;      
    }
    if (!changed){ return commitToTable(g,bs, l, rcc); }
    var ms= Collections.unmodifiableList(res);
    IT t= rcc.withTs(ts);
    return commitToTable(g, bs, l.withMsT(ms, t), t);
  }
  private E commitToTable(Gamma g, List<B> bs, E.Literal l, IT t){
    TName name= l.name();
    if (!t.isTV() || !(t instanceof IT.RCC rcc) || hasU(l.ms()) || meths.cache().containsKey(name)){ return l; }
    var freeNames= Stream.of(
      new FreeXs(g).ftvMs(l.ms()),
      new FreeXs(g).ftvCs(l.cs()),
      new FreeXs(g).ftvT(t)
      ).flatMap(s->s);
    List<B> localBs= freeNames.distinct().map(x -> RC.get(bs, x)).toList();
    TName newName= name.withArity(localBs.size());
    List<M> ms= fixArity(l.ms(), name, newName);
    Optional<RC> orc= l.rc().or(()->Optional.of(rcc.rc()));
    if (!l.infName()){
      l = new E.Literal(orc, newName, localBs, l.cs(), l.thisName(), ms, l.t(), l.src(),l.infName(), l.infHead(), l.g());
      assert !meths.cache().containsKey(name);
      var resD= meths.injectDeclaration(l);
      meths.cache().remove(name);
      meths.cache().put(resD.name(), resD);
      return l;
    }
    assert l.bs().isEmpty() : "bs must stay empty pre-commit";
    var noMeth= l.ms().stream().allMatch(m -> m.impl().isEmpty());
    if (noMeth && l.infHead() && meths._from(rcc.c().name()) != null){ return new E.Type(rcc, rcc, l.src(), l.g()); }
    var selfInferred= rcc.c().name().equals(l.name());
    List<IT.C> cs= selfInferred? meths.fetchCs(rcc.c()) : Push.of(rcc.c(), meths.fetchCs(rcc.c()));
    meths.checkMagicSupertypes(l, cs);
    assert l.infHead();
    l = new E.Literal(orc, newName, localBs, cs, l.thisName(), ms, t, l.src(),l.infName(), l.infHead(), l.g());
    core.E.Literal resD= meths.injectDeclaration(l);
    assert !meths.cache().containsKey(name);
    meths.cache().put(resD.name(), resD);
    return l;
  }
  private M fixArity(M m, TName name, TName newName){
    var s= m.sig();
    assert s.origin().isPresent();
    if (!s.origin().get().equals(name)){ return m; }
    return m.withSig(s.withOrigin(newName));
  }
  private static boolean hasU(List<inference.M> ms){
    return !ms.stream()
      .allMatch(m -> m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t -> t.get().isTV()));
  }
  private List<Optional<IT>> updateArgs(List<String> xs, List<Optional<IT>> old, Gamma g){
    return norm(old,Streams.zip(xs, old).map((x,oi)->{
      if ("_".equals(x)){ return oi; }
      var ti= Optional.of(meetKeepLeft(oi.get(), g.get(x)));
      return oi.equals(ti)? oi:ti;
    }).toList());
  }
  record TSM(List<IT> ts, inference.M m){}
  //-----
  TSM nextMStarAbs(boolean committed, IT.RCC rcc, inference.M m){
    assert m.impl().isEmpty();
    if(committed){ return new TSM(rcc.c().ts(), m); }
    var improvedSig= m.sig();
    var omh= methodHeaderAnd(rcc, improvedSig.m().get(), improvedSig.rc(),(_,_,mi)->mi);
    assert omh.isEmpty() || assertNoBinderClash(rcc, omh.get());
    if (omh.isEmpty()){ return new TSM(rcc.c().ts(), m); }
    var rcc0= rcc.withTs(refineClsTsFromHeader(rcc.c().ts(), rcc, improvedSig, omh.get().sig()));
    var sigRes= normalizeSigAgainstHeader(rcc0, improvedSig);
    var newTs= dropMethBsFromClsTs(rcc0, improvedSig);
    if (sigRes.equals(improvedSig)){ return new TSM(newTs, m); }
    return new TSM(newTs, new inference.M(sigRes, Optional.empty()));
  }
  TSM nextMStarOp(List<B> bs, Gamma g, String thisN, boolean committed, Optional<IT.RCC> selfPrecise, IT.RCC rcc, inference.M m){
    assert m.impl().isPresent();
    g.newScope();
    g.declare(thisN, selfTFor(selfPrecise,rcc,m.sig().rc().get()));
    updateGWithArgs(g, m);
    var e= nextStar(Push.of(bs, m.sig().bs().get()), g, m.impl().get().e());
    var args= updateArgs(m.impl().get().xs(), m.sig().ts(), g);
    g.popScope();
    if(!committed){ return nextMStarOpRun(rcc,m,e,args); }  
    if (e == m.impl().get().e()){ return new TSM(rcc.c().ts(), m); }
    return new TSM(rcc.c().ts(), new inference.M(m.sig(), Optional.of(m.impl().get().withE(e))));
  }
  TSM nextMStarOpRun(IT.RCC rcc, inference.M m, E e, List<Optional<IT>> args){
    M.Sig improvedSig= m.sig().withTsT(args, meetKeepLeft(m.sig().ret().get(), e.t()));
    var omh= methodHeaderAnd(rcc, improvedSig.m().get(), improvedSig.rc(),(_,_,mi)->mi);
    assert omh.isEmpty() || assertNoBinderClash(rcc, omh.get());
    return omh
      .map(mh->headerResult(rcc,m,e,mh.sig(),improvedSig))
      .orElseGet(()->noHeaderResult(rcc,m,e,improvedSig));
  }
  private void updateGWithArgs(Gamma g, inference.M m) {
    var xs= m.impl().get().xs();
    var args0= m.sig().ts();
    assert xs.size() == args0.size();
    assert m.sig().m().get().arity() == xs.size();
    for (int i= 0; i < xs.size(); i += 1){ g.declare(xs.get(i), args0.get(i).get()); }
  }
  private static IT selfTFor(Optional<IT.RCC> selfPrecise,IT.RCC rcc,RC mrc){
    RC thisRc= (mrc == RC.read && rcc.rc() == RC.imm) ? RC.imm : mrc;
    return selfPrecise.<IT>map(it->it.withRC(thisRc)).orElse(IT.U.Instance);
  }
  TSM headerResult(IT.RCC rcc, inference.M m, E e, core.Sig sig, M.Sig improvedSig){
    var rcc0= rcc.withTs(refineClsTsFromHeader(rcc.c().ts(), rcc, improvedSig,sig));
    var sigRes= normalizeSigAgainstHeader(rcc0, improvedSig);
    var impl1= m.impl().get().withE(meet(e, sigRes.ret().get()));
    var newTs= dropMethBsFromClsTs(rcc0, improvedSig);
    if (sigRes.equals(m.sig()) && impl1 == m.impl().get()){ return new TSM(newTs, m); }
    return new TSM(newTs, new inference.M(sigRes, Optional.of(impl1)));
  }
  private List<IT> refineClsTsFromHeader(List<IT> ts, IT.RCC rcc, M.Sig improvedSig, core.Sig imh){
    var Xs= getDec(rcc.c().name()).bs().stream().map(b -> b.x()).toList();
    return meetKeepLeft(Stream.of(
      Stream.of(ts),
      IntStream.range(0, imh.ts().size()).mapToObj(i -> refine(Xs,imh.ts().get(i), improvedSig.ts().get(i))),
      Stream.of(refine(Xs,imh.ret(), improvedSig.ret()))
    ).flatMap(z->z).toList());
  }
  private List<IT> refine(List<String> Xs, core.T t,Optional<IT> it){return refine(Xs,TypeRename.tToIT(t), it.get()); }
  private M.Sig normalizeSigAgainstHeader(IT.RCC rcc, M.Sig improvedSig){
    var targetBs= improvedSig.bs().isEmpty()
      ? List.<String>of()
      : improvedSig.bs().get().stream().map(B::x).toList();
    MSigL h= methodHeader(rcc, improvedSig.m().get(), improvedSig.rc()).get();
    assert h.bsArity() == targetBs.size();
    return improvedSig.withTsT(
      h.psStr(improvedSig.span(), targetBs),
      h.retStr(improvedSig.span(), targetBs));
  }
  private List<IT> dropMethBsFromClsTs(IT.RCC rcc, M.Sig improvedSig){
    var methBs= improvedSig.bs().get().stream().map(b->b.x()).toList();
    return dropMethBs(rcc.c().ts(), methBs);
  }
  private TSM noHeaderResult(IT.RCC rcc, inference.M m, E e, M.Sig improvedSig){
    var impl1= m.impl().get().withE(meet(e, improvedSig.ret().get()));
    if (improvedSig.equals(m.sig()) && impl1 == m.impl().get()){ return new TSM(rcc.c().ts(), m); }
    return new TSM(rcc.c().ts(), new inference.M(improvedSig, Optional.of(impl1)));
  }
  List<IT> dropMethBs(List<IT> ts, List<String> methBs){
    if (methBs.isEmpty()){ return ts; }
    return norm(ts,ts.stream().map(t->dropMethBs(t, methBs)).toList());
  }
  IT dropMethBs(IT t, List<String> methBs){ return switch (t){
    case IT.X x -> methBs.contains(x.name()) ? IT.U.Instance : t;
    case IT.RCX(_,var x) -> methBs.contains(x.name()) ? IT.U.Instance : t;
    case IT.ReadImmX(var x) -> methBs.contains(x.name()) ? IT.U.Instance : t;
    case IT.RCC rcc -> rcc.withTs(dropMethBs(rcc.c().ts(), methBs));
    case IT.U _ -> t;
    case IT.Err _ -> t;
  };}
  private boolean assertNoBinderClash(IT.RCC rcc, core.M m){
    var cls= getDec(rcc.c().name()).bs().stream().map(B::x).toList();
    var meth= m.sig().bs().stream().map(B::x).toList();
    return Collections.disjoint(cls, meth);
  }
  List<IT> refine(List<String> xs, IT t, IT t1){
    if (t1 instanceof IT.U){ return qMarks(xs.size()); }
    return switch (t){
      case IT.X x -> refineXs(xs, x, t1);
      case IT.RCX(RC _, IT.X x) -> refineXs(xs, x, stripOuterView(t1));
      case IT.ReadImmX(IT.X x) -> refineXs(xs, x, stripOuterView(t1));
      case IT.RCC(RC _, IT.C c,_) -> propagateXs(xs, c, t1);
      case IT.U _ -> qMarks(xs.size());
      case IT.Err _ -> qMarks(xs.size());
    };
  }
  static IT stripOuterView(IT t){ return switch (t){
    case IT.RCC rcc -> rcc.withRC(RC.imm);
    case IT.RCX(RC _, var x) -> x;
    case IT.ReadImmX(var x) -> x;
    default -> t;
  };}
  List<IT> refineXs(List<String> xs, IT.X x, IT t1){
    var i= xs.indexOf(x.name());
    if (i == -1 ){ return qMarks(xs.size()); }
    return qMarks(i, t1, xs.size());
  }
  //---to use instead of just best
  private List<IT.C> supersWithHead(IT.C self, TName head){
    var d= meths._from(self.name());
    if (d == null){ return List.of(); } // {..}.foo etc.
    var hits= d.cs().stream().filter(sc -> sc.name().equals(head)).distinct().toList();
    if (hits.isEmpty()){ return List.of(); }
    List<String> xs= d.bs().stream().map(B::x).toList();
    return TypeRename.ofITC(TypeRename.tcToITC(hits), xs, self.ts());
  }
  private Optional<IT.RCC> viewAs(IT.RCC t, TName head){//TODO: see where the use is commented and for a test distinguishing the use
    //there is one test now changing, but it is a strange case.
    if (t.c().name().equals(head)){ return Optional.of(t); }
    var hits= supersWithHead(t.c(), head);
    if (hits.isEmpty()){ return Optional.empty(); }
    assert hits.size() == 1 : "Ambiguous viewAs "+t.c().name()+" as "+head+": "+hits;
    return Optional.of(new IT.RCC(t.rc(), hits.getFirst(), t.span()));
  }
  private Stream<IT.C> viewCs(IT.C self, TName head){
    //return Stream.of(self);
    if (self.name().equals(head)){ return Stream.of(self); }
    return supersWithHead(self, head).stream();
  }
  //---
  private List<IT> bindArgs(List<String> xs, List<IT> templArgs, List<IT> actualArgs){
    assert templArgs.size() == actualArgs.size();
    List<List<IT>> parts= IntStream.range(0, templArgs.size())
      .mapToObj(i -> refine(xs, templArgs.get(i), actualArgs.get(i)))
      .toList();
    return parts.isEmpty() ? qMarks(xs.size()) : meetKeepLeft(parts);
  }
  List<IT> propagateXs(List<String> xs, IT.C templ, IT t1){
    if (t1 instanceof IT.U || t1 instanceof IT.Err){ return qMarks(xs.size()); }
    if (!(t1 instanceof IT.RCC act)){ return qMarks(xs.size()); }
    var cands= new ArrayList<List<IT>>();
    viewCs(act.c(), templ.name())
      .forEach(sc -> cands.add(bindArgs(xs, templ.ts(), sc.ts())));
    var actHead= act.c().name();
    viewCs(templ, actHead)
      .forEach(sc -> cands.add(bindArgs(xs, sc.ts(), act.c().ts())));
    return cands.isEmpty() ? qMarks(xs.size()) : meetKeepLeft(cands);
  }
  static <TT> List<TT> norm(List<TT> original, List<TT> candidate){
    if (candidate == original){ return original; }
    int n= original.size();
    assert candidate.size() == n;
    for (int i= 0; i < n; i++){ if (candidate.get(i) != original.get(i)){ return candidate; } }
    return original;
  }
  private static boolean needsPrototypeAscription(E.Literal l){
    if (l.infHead() || !l.infName() || !l.cs().isEmpty()){ return false; }
    return (l.t() instanceof IT.U /*&& l.ms().stream().anyMatch(m-> !m.sig().isFull())*/);
  }
  private E prototypeAscribeRootReceiver(E arg, IT expected){
    if (!(expected instanceof IT.RCC exp)){ return arg; }
    return switch (arg){
      case E.Call c -> c.withE(prototypeAscribeRootReceiver(c.e(), expected));
      case E.ICall c -> c.withE(prototypeAscribeRootReceiver(c.e(), expected));
      case E.Literal l -> needsPrototypeAscription(l)
        ? l.withT(prototypeHead(exp,l.span()))
        : arg;
      default -> arg;
    };
  }
  private IT.RCC prototypeHead(IT.RCC expected, TSpan span){
    return new IT.RCC(expected.rc(), new IT.C(expected.c().name(), qMarks(expected.c().ts().size())), span);
  }
}
record MSigL(RC rc, List<String> xs, List<IT> clsArgs, List<IT> ps0, IT ret0){
  int arity(){ return ps0.size(); }
  int nCls(){ return clsArgs.size(); }
  int bsArity(){ return xs.size() - nCls(); }
  List<String> methXs(){ return xs.subList(nCls(), xs.size()); }
  IT p(int i, List<IT> targs){ return inst(ps0.get(i), targs); }
  IT ret(List<IT> targs){ return inst(ret0, targs); }
  MSigL withClsArgs(List<IT> clsArgs){
    if (clsArgs.equals(this.clsArgs)){ return this; }
    assert clsArgs.size() == this.clsArgs.size();
    return new MSigL(rc, xs, clsArgs, ps0, ret0);
  }
  private IT inst(IT t, List<IT> targs){//Note: this will eventually become an error at type system time.
    targs = fixTargs(targs, bsArity());
    var ts= Push.of(clsArgs,targs);//performance? we could cache this result since targs is fixed and used over and over
    return TypeRename.of(t, xs, ts);
  }
  static IT arityErr(){ return IT.Err.merge(IT.U.Instance, IT.U.Instance); }
  static List<IT> fixTargs(List<IT> targs, int n){
    int k= targs.size();
    if (k == n){ return targs; }
    if (k > n){ return targs.subList(0, n); }
    return Stream.concat(
      targs.stream(),
      IntStream.range(0, n-k).mapToObj(_->arityErr())
      ).toList();
  }
  IT pStr(TSpan span, int i, List<String> targetBs){ return inst(ps0.get(i), toXs(span,targetBs)); }
  List<Optional<IT>> psStr(TSpan span,List<String> targetBs){
    assert targetBs.size() == bsArity();
    var ts= toXs(span, targetBs);
    return ps0.stream().map(p->Optional.of(inst(p, ts))).toList();
  }
  IT retStr(TSpan span,List<String> targetBs){
    assert targetBs.size() == bsArity();
    return inst(ret0, toXs(span,targetBs));
  }
  private List<IT> toXs(TSpan span,List<String> targetBs){ return targetBs.stream().<IT>map(n->new IT.X(n,span)).toList(); }
}