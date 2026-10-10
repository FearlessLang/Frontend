package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.LiteralDeclarations;
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
import typeSystem.TypeSystem;
import utils.OneOr;
import utils.Push;
import utils.Range;
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
    //No! at this point they have been (correctly) divided in layers assert tops.stream().sorted().toList().equals(tops);
    return tops.stream()
      .map(l->s.stepDec(meths.cache().get(l.name()), l)).toList();
  }
  private core.E.Literal stepDec(core.E.Literal di, inference.E.Literal li){ return di.withMs(li.ms().stream().map(m->stepDecM(di, m)).toList()); }
  private boolean sameM(core.Sig s1, inference.M.Sig s2){
    return s1.m().equals(s2.m().get()) && s1.rc() == s2.rc().orElse(RC.imm);
  }
  private core.M stepDecM(core.E.Literal di, inference.M m){
    var mCore= OneOr.of("Method mismatch", di.ms().stream().filter(mi->sameM(mi.sig(), m.sig())));
    if (m.impl().isEmpty()){ return mCore; }//assert same type as m lifted to core
    var e= m.impl().get().e();
    var span= di.name().approxSpan();
    var xs= m.impl().get().xs();
    var thisType= new IT.RCC(Optional.of(mCore.sig().rc()), new IT.C(di.name(), MSigL.toXs(span,B.xs(di.bs()))),span);//no preferred on self names
    var ei= meet(e, TypeRename.tToIT(mCore.sig().ret()));
    var g= Gamma.of(xs, TypeRename.tToIT(mCore.sig().ts()), di.thisName(), thisType);
    var bs= Push.of(di.bs(), m.sig().bs().get());
    ei= nextStar(bs, g, ei);
    return new core.M(mCore.sig(), xs, Optional.of(new ToCore(bs).of(ei, e)));
  }
  E meet(E e, IT t){
    if (e instanceof E.Type tt){ return nextT(tt); }
    var typedLit= e instanceof E.Literal l && l.t().isTV();
    if (typedLit){ return e; }
    e= prototypeAscribeRootReceiver(e, t, false);
    return e.withT(meet(e.t(), t));
  }
  private long badnessAs(RCC src, TName targetHead){
    assert !src.c().name().equals(targetHead);
    return adaptedSuperTs(src, targetHead).getFirst().badness();
  }
  private IT leastBad(RCC a, RCC b){
    var aSuper= isASuperB(a.c().name(), b.c().name()); // a is super of b
    var bSuper= isASuperB(b.c().name(), a.c().name()); // b is super of a
    var aBad= bSuper ? Math.max(badnessAs(a, b.c().name()),a.badness()) : a.badness();
    var bBad= aSuper ? Math.max(badnessAs(b, a.c().name()),b.badness()) : b.badness();
    //Cases considered: A[?] < B[?,?] vs B[X,?] = B[X,?] win;   A[?] < B vs A[T] = A[T] win
    if (aBad != bBad){ return aBad < bBad ? a : b; }
    if (aSuper){ return b; }
    if (bSuper){ return a; }
    if (a.depth() != b.depth()){ return a.depth() < b.depth() ? a : b; }
    return a.c().name().s().compareTo(b.c().name().s()) < 0 ? a : b;
  }
  private IT leastBad(IT a, IT b){
    assert !(a instanceof IT.U);
    assert !(b instanceof IT.U);
    if (a instanceof RCC){ return a; }
    if (b instanceof RCC){ return b; }
    var aRcOverBareB= a instanceof IT.RCX && (b instanceof IT.X || b instanceof IT.ReadImmX);
    if (aRcOverBareB){ return a; }
    var bRcOverBareA= b instanceof IT.RCX && (a instanceof IT.X || a instanceof IT.ReadImmX);
    if (bRcOverBareA){ return b; }
    return a.toString().compareTo(b.toString()) < 0 ? a : b;
  }
  IT meet(IT t1, IT t2){
    if (t2 instanceof IT.U){ return t1; }
    if (t1 instanceof IT.U){ return t2; }
    if (t1.equals(t2)){ return t1; }
    var t1ReadImmOfT2= t1 instanceof IT.ReadImmX(var x1) && x1.equals(t2);
    if (t1ReadImmOfT2){ return t1; }
    var t2ReadImmOfT1= t2 instanceof IT.ReadImmX(var x2) && x2.equals(t1);
    if (t2ReadImmOfT1){ return t2; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.c().name().equals(x2.c().name())){ return leastBad(x1,x2); }
      var rc= meetRcNoH(x1.rc(), x2.rc());
      return x1.withRCTs(rc,meet(x1.c().ts(), x2.c().ts()));
    }
    if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX(var rc2, var x2))){ return leastBad(t1, t2); }
    if (!x1.x().equals(x2)){ return leastBad(t1, t2); }
    return x1.withRC(meetRcNoH(Optional.of(x1.rc()), Optional.of(rc2)).get());
  }
  static Optional<RC> meetRcNoH(Optional<RC> a, Optional<RC> b){
    if (a.isEmpty()){ return b; }
    if (b.isEmpty()){ return a; }
    var x= noH(a.get());
    var y= noH(b.get());
    var keepX= x == y || y == RC.iso || y == RC.read && x != RC.iso;
    if (keepX){ return Optional.of(x); }
    if (x == RC.iso || x == RC.read){ return Optional.of(y); }
    return Optional.of(RC.imm);// returning Optional.empty(); could make it go in loop
  }
  static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
  List<IT> meet(List<IT> t1, List<IT> t2){ return Streams.zip(t1, t2).map(this::meet).toList(); }
  List<IT> meet(List<List<IT>> tss){ return tss.stream().reduce(this::meet).get(); }
  E nextStar(List<B> bs, Gamma g, E e){
    var start= e;
    if (e.done(g)){ return e; }
    while (true){
      var s= g.snapshot();
      var oe= next(bs, g, e);
      assert oe == e || !oe.equals(e) : "Allocated equal E:"+e.getClass()+"\n"+e;
      var stable= oe == e && !g.changed(s);
      if (stable){
        e.sign(g);
        assert e == start || !e.equals(start);
        return e;
      }
      //if (oe.equals(e) && !g.changed(s)){ e.sign(g); return e; }//this line is useful for debugging when == gets buggy
      e= oe;
    }
  }
  private List<E> nextStar(List<B> bs, Gamma g, List<E> es){
    return norm(es,es.stream().map(ei->nextStar(bs, g, ei)).toList());
  }
  private List<E> meetWithTargs(List<E> originEs,List<E> es, MSigL m, List<IT> targs){
    var res= norm(es,Streams.zip(es, m.ps0()).map((e,p)->meet(e, m.inst(p,targs))).toList());
    assert notBackToOrigin(originEs, res);
    return res;
  }
  private boolean notBackToOrigin(List<E> originEs, List<E> res){
    //complex but invaluable: if it fails it means we are going 'back and forth'
    //and this could cause loops.
    return Streams.zip(res, originEs).allMatch((r,o)->r == o || !r.equals(o));
  }
  E next(List<B> bs, Gamma g, E e){
    try{
      //assert meet(e.t(),res.t()).equals(res.t()): e.t()+" "+res.t();// Does not hold. How can it be?
      return switch (e){
        case E.X x -> nextX(g, x);
        case E.Literal l -> nextL(bs, g, l);
        case E.Call c -> nextC(bs, g, c);
        case E.ICall c -> nextIC(bs, g, c);
        case E.Type c -> nextT(c);
      };
    }
    catch(WellFormednessErrors.ErrToFetchContext depthErr){ throw meths.p().err().itTooDeep(e,depthErr.c); }
  }
  private IT preferred(IT.RCC type){
    var d= meths.from(type.c().name());//d.cs() does contain all the transitive supertypes already.
    var c= OneOr.opt("Repeated WidenTo supertype", d.cs().stream().filter(ci->ci.name().equals(LiteralDeclarations.widen)));
    if (c.isEmpty()){ return type; }
    var wid= TypeRename.of(TypeRename.tToIT(OneOr.of("WidenTo has one type argument", c.get().ts().stream())), B.xs(d.bs()), type.c().ts());
    if (!(wid instanceof IT.RCC(_, var widC, _))){ return type; }
    return new IT.RCC(type.rc(), widC,type.span());
  }
  private RC overloadNorm(Optional<RC> rc){ return rc.map(r->r == RC.iso ? RC.imm : noH(r)).orElse(RC.imm); }
  private Optional<core.M> oneFromGuessRC(List<core.M> ms, RC rc){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    var readOne= OneOr.opt("not well formed ms", ms.stream().filter(m->m.sig().rc() == RC.read));
    var mutOne= OneOr.opt("not well formed ms", ms.stream().filter(m->m.sig().rc() == RC.mut));
    var immOne= OneOr.opt("not well formed ms", ms.stream().filter(m->m.sig().rc() == RC.imm));
    if (rc == RC.read){ return readOne.or(()->immOne).or(()->mutOne); }
    if (rc == RC.mut){ return mutOne.or(()->readOne).or(()->immOne); }
    assert rc == RC.imm;
    return immOne.or(()->readOne).or(()->mutOne);
  }
  private <R> Optional<R> methodHeaderAnd(IT.RCC rcc, MName name, Optional<RC> favorite, BiFunction<core.E.Literal,core.M,R> f){
    var d= meths._from(rcc.c().name());
    if (d == null){ return Optional.empty(); }//case {..}.foo
    var ms= d.ms().stream().filter(m->m.sig().m().equals(name));
    var om= favorite
      .map(rc->OneOr.opt("Ambiguous method header for explicit RC", ms.filter(mi->mi.sig().rc() == rc)))
      .orElseGet(()->oneFromGuessRC(ms.toList(), overloadNorm(rcc.rc())));
    return om.map(mm->f.apply(d, mm));
  }
  private MSigL methodHeaderInstance(IT.RCC rcc, core.E.Literal d, core.M m){
    var clsXs= B.xs(d.bs());
    assert clsXs.stream().distinct().count() == clsXs.size();
    var methXs= B.xs(m.sig().bs());
    assert methXs.stream().distinct().count() == methXs.size();
    assert Collections.disjoint(clsXs, methXs);
    var clsArgs= rcc.c().ts();
    assert clsArgs.size() == clsXs.size();
    var xs= Push.of(clsXs,methXs);//TODO: could avoid materializing the two lists
    var ps0= TypeRename.tToIT(m.sig().ts());
    var ret0= TypeRename.tToIT(m.sig().ret());
    return new MSigL(m.sig().rc(), xs, d.bs(), clsArgs, m.sig().bs(), ps0, ret0);
  }
  Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){
    return methodHeaderAnd(rcc, name, favorite, (d,m)->methodHeaderInstance(rcc, d, m));
  }
  static List<IT> qMarks(int n){ return Stream.<IT>generate(()->IT.U.Instance).limit(n).toList(); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i->i == n ? t : IT.U.Instance).toList(); }
  private E nextX(Gamma g, E.X x){
    var t1Base= g.get(x.name());
    var notIn= g.notFunnelledInto(x.name());
    if (notIn.isPresent()){ throw meths.p().err().captureNotFunnelled(x, t1Base, notIn.get()); }
    var t1= g.getWithRC(x.name());
    var t2= x.t();
    if (t1.equals(t2)){ return x; }
    if (!(t2 instanceof IT.U)){ updateG(g, x.name(), t1Base, t2); }
    return x.withT(meet(t1, t2));
  }
  private void updateG(Gamma g, String x, IT t1, IT t2){
    if (t1 instanceof IT.U){ g.update(x, t2); return; }
    if (t1 instanceof IT.RCC(var aRc, var aC, var aSpan) && t2 instanceof IT.RCC(var bRc, var bC, _)){
      if (aC.name().equals(bC.name())){ g.update(x, new RCC(glbRcNoH(aRc, bRc), aC, aSpan)); }
      return;
    }
    if (!(t1 instanceof IT.RCX a && t2 instanceof IT.RCX(var bRc, var bX))){ return; }
    if (a.x().equals(bX)){ g.update(x, a.withRC(glbRcNoH(a.rc(), bRc))); }
  }
  static Optional<RC> glbRcNoH(Optional<RC> a, Optional<RC> b){
    if (a.isEmpty()){ return b; }
    if (b.isEmpty()){ return a; }
    return Optional.of(glbRcNoH(a.get(), b.get()));
  }
  static RC glbRcNoH(RC a, RC b){
    a= noH(a); b= noH(b);
    if (a == b){ return a; }
    if (a == RC.read){ return b; }
    if (b == RC.read){ return a; }
    return RC.iso;
  }
  private E nextT(E.Type t){
    if (!(t.t() instanceof IT.U)){ return t; }
    return t.withT(preferred(t.type()));
  }
  private E nextIC(List<B> bs, Gamma g, E.ICall c){
    var e= nextStar(bs, g, c.e());
    var es= nextStar(bs, g, c.es());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, es); }
    var om= methodHeader(rcc, c.name(), Optional.empty());
    if (om.isEmpty()){ return c.withEEs(e, es); }
    var m= om.get();
    var ts= qMarks(m.bsArity());
    var call= new E.Call(e, c.name(), Optional.of(m.rc()), ts, meetWithTargs(es, es, m, ts), c.src());
    return call.withT(meet(c.t(), m.ret(ts)));
  }
  private E nextC(List<B> bs, Gamma g, E.Call c){
    var e= nextStar(bs, g, c.e());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    var om= methodHeader(rcc, c.name(), c.rc());
    if (om.isEmpty()){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    var m= om.get();
    var es= nextStar(bs, g, requiredOnArgs(bs, c, m));
    assert es == c.es() || !es.equals(c.es());
    assert m.ps0().size() == es.size();
    var all= newAllTs(c, es, m);
    assert all.size() == m.nCls()+m.bsArity();
    var clsTs= normToBounds(bs,m.clsBs(),all.subList(0, m.nCls()));
    var targs= normToBounds(bs,m.methBs(),all.subList(m.nCls(), all.size()));
    e= meet(e, rcc.withTs(clsTs));
    m= m.withClsArgs(clsTs);
    var it= meet(c.t(), m.ret(targs));
    var es1= meetWithTargs(c.es(),es, m, targs);
    var noChange= e == c.e() && es1 == c.es() && targs.equals(c.targs()) && it.equals(c.t());
    if (noChange){ return c; }
    return c.withMore(e, c.rc().orElse(m.rc()), targs, es1, it);
  }
  private List<E> requiredOnArgs(List<B> bs, E.Call c, MSigL m){
    var all= decidedThen(c, m, c.es(), Stream.of());
    var m0= m.withClsArgs(normToBounds(bs, m.clsBs(), all.subList(0, m.nCls())));
    return meetWithTargs(c.es(), c.es(), m0, normToBounds(bs, m.methBs(), all.subList(m.nCls(), all.size())));
  }
  private List<IT> newAllTs(E.Call c, List<E> es, MSigL m){
    return decidedThen(c, m, es, Streams.zip(m.ps0(), es).map((p,e2)->refine(m.xs(), p, e2.t())));
  }
  private List<IT> decidedThen(E.Call c, MSigL m, List<E> es, Stream<List<IT>> argRefinements){
    var targs= MSigL.fixTargs(c.targs(), m.bsArity());
    var all= meet(Streams.of(Stream.of(Push.of(m.clsArgs(), targs)), argRefinements, Stream.of(refine(m.xs(), m.ret0(), c.t()))).toList());
    var written= Push.of(m.clsArgs(), writtenTargs(c) ? targs : qMarks(m.bsArity()));
    var fromLiterals= Streams.zip(m.ps0(), es).filter((_,e2)->e2 instanceof E.Literal).map((p,e2)->refine(m.xs(), p, e2.t()));
    var hard= meet(Streams.of(Stream.of(qMarks(written.size())), fromLiterals).toList());
    var fixed= Streams.zip(written, hard).map((w,h)->decided(w) ? w : h).toList();
    return Streams.zip(fixed, all).map((b,r)->decided(b) ? b : r).toList();
  }
  private static boolean writtenTargs(E.Call c){ return c.src().inner instanceof fearlessFullGrammar.E.Call sc && sc.targs().isPresent(); }
  private static boolean decided(IT t){ return t.isTV() && !(t instanceof IT.RCC(var rc, _, _) && rc.isEmpty()); }
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    var selfUnknown= l.infName() && l.rc().isEmpty();
    if (selfUnknown){ return Optional.empty(); }
    var span= l.name().approxSpan();
    return Optional.of(new IT.RCC(l.rc(), new IT.C(l.name(), MSigL.toXs(span,B.xs(l.bs()))),span));
  }
  private Optional<IT.RCC> superSelf(E.Literal l, Optional<IT.RCC> precise){
    if (l.cs().size() != 1){ return precise; }
    return precise.map(p->new IT.RCC(p.rc(), l.cs().getFirst(), p.span()));
  }
  private E nextL(List<B> bs, Gamma g, E.Literal l){
    var infHead= l.infHead();//infHead is set in l.withCsMs and l.withMsT
    // to mean the HEAD is inferred as IT.RCC and has already been used to expand methods
    var selfPrecise= preciseSelf(l);
    var selfSuper= superSelf(l,selfPrecise);
    if (!infHead){
      l= l.infName() ? selfSuper.map(l::withT).orElse(l) : l.withT(selfPrecise.get());
      if (!(l.t() instanceof IT.RCC(_, var c, _))){ return l; }//!infHead after passing this test means right now we can expand methods
      l= l.infName() && !c.name().equals(l.name()) ? meths.expandLiteral(l, c, bs) : meths.expandDeclaration(l,true);
    }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    var res= new ArrayList<inference.M>(l.ms().size());
    var ts= rcc.c().ts();
    for (var mi : l.ms()){
      assert mi.impl().isEmpty() || selfPrecise.isEmpty() || rcc.isTV();
      var rcci= withTsNormBs(rcc,ts);
      var next= mi.impl().isEmpty() ? nextMStarAbs(rcci, mi) : nextMStarOp(bs, g, l, selfPrecise, rcci, mi);
      assert next.m == mi || !next.m.equals(mi);
      ts= meet(ts, next.ts);
      res.add(next.m);
    }
    var ms= norm(l.ms(),Collections.unmodifiableList(res));
    var noChange= ms == l.ms() && ts.equals(rcc.c().ts());
    if (noChange){ return commitToTable(g,bs, l, rcc); }
    var t= withTsNormBs(rcc,ts);
    return commitToTable(g, bs, l.withMsT(ms, t), t);
  }
  private E commitToTable(Gamma g, List<B> bs, E.Literal l, IT.RCC rcc){
    var name= l.name();
    var notReady= !rcc.isTV() || hasU(l.ms()) || meths.cache().containsKey(name);
    if (notReady){ return l; }
    var freeNames= Streams.of(new FreeXs(g).ftvMs(l.ms()), new FreeXs(g).ftvCs(l.cs()), rcc.ftv());
    var localBs= freeNames.distinct().map(x->B.get(bs, x)).toList();
    var newName= name.withArity(localBs.size());
    var ms= fixArity(l.ms(), name, newName);
    var orc= l.rc().or(rcc::rc).map(InjectionSteps::noH);
    assert l.infName();
    assert l.bs().isEmpty();
    var noMeth= l.ms().stream().allMatch(m->m.impl().isEmpty());
    var justAType= noMeth && l.infHead() && meths._from(rcc.c().name()) != null;
    var orcc= new IT.RCC(orc, rcc.c(), rcc.span());
    if (justAType){ return new E.Type(orcc, preferred(orcc), l.src(), l.g()); }
    var selfInferred= rcc.c().name().equals(l.name());
    var cs= selfInferred ? meths.fetchCs(rcc.c()) : Push.of(rcc.c(), meths.fetchCs(rcc.c()));
    meths.checkMagicSupertypes(l, cs);
    assert l.infHead();
    l= new E.Literal(orc, newName, localBs, cs, l.thisName(), ms, rcc, l.src(),l.infName(), l.infHead(), l.g());
    if (selfInferred){ l= l.withT(preciseSelf(l).get()); }
    assert !meths.cache().containsKey(name);
    meths.register(l);
    return l;
  }
  private List<M> fixArity(List<M> ms, TName name, TName newName){
    if (name.equals(newName)){ return ms; }
    return norm(ms,ms.stream().map(mi->fixArity(mi, name, newName)).toList());
  }
  private M fixArity(M m, TName name, TName newName){
    var s= m.sig();
    if (!s.origin().get().equals(name)){ return m; }
    return m.withSig(s.withOrigin(newName));
  }
  private static boolean hasU(List<inference.M> ms){
    return !ms.stream()
      .allMatch(m->m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t->t.get().isTV()));
  }
  private List<Optional<IT>> updateArgs(inference.M m, Gamma g){
    return Streams.zip(m.impl().get().xs(), m.sig().ts()).map((x,oi)->x.equals("_") ? oi : Optional.of(meet(oi.get(), g.get(x)))).toList();
  }
  record TSM(List<IT> ts, inference.M m){}
  TSM nextMStarAbs(IT.RCC rcc, inference.M m){
    assert m.impl().isEmpty();
    var omh= methodHeaderAnd(rcc, m.sig().m().get(), m.sig().rc(),(_,mi)->mi);
    assert omh.stream().allMatch(mh->assertNoBinderClash(rcc, mh));
    if (omh.isEmpty()){ return new TSM(rcc.c().ts(), m); }
    var rcc0= withTsNormBs(rcc,refineClsTsFromHeader(rcc, m.sig(), omh.get().sig()));
    return new TSM(dropMethBsFromClsTs(rcc0, m.sig()), m.withSig(normalizeSigAgainstHeader(rcc0, m.sig())));
  }
  TSM nextMStarOp(List<B> bs, Gamma g, E.Literal l, Optional<IT.RCC> selfPrecise, IT.RCC rcc, inference.M m){
    assert m.impl().isPresent();
    var litBs= l.infName() ? bs : l.bs();
    g.newScope(m.sig().rc().get(), litBs, l);
    g.declare(l.thisName(), selfPrecise.<IT>map(s->new IT.RCC(s.rc().map(RC::isoToMut), s.c(), s.span())).orElse(IT.U.Instance));
    g.newScope(m.sig().rc().get(), litBs, l);
    assert m.sig().m().get().arity() == m.impl().get().xs().size();
    Streams.zip(m.impl().get().xs(), m.sig().ts()).forEach((x,t)->g.declare(x, t.get()));
    var e= nextStar(Push.of(litBs, m.sig().bs().get()), g, meet(m.impl().get().e(), m.sig().ret().get()));
    var args= updateArgs(m, g);
    g.popScope();
    g.popScope();
    return nextMStarOpRun(rcc, m, e, args);
  }
  /*The meet below narrows a method's return type to the type of its body, so a literal only ever
  gets more precise than what the use site asked for. What keeps that from destroying an invariant
  instantiation is that a decided type argument is never re-decided: requiredOnArgs and the meet in
  nextMStarOp push what is already known down before a body is inferred, and keepDecided then only
  fills the type arguments still unknown. See the five tests named in TypeSystemTest, next to
  blockLetInfersItsTypeFromTheLambdaBody, for what base needs the meet itself for.*/
  TSM nextMStarOpRun(IT.RCC rcc, inference.M m, E e, List<Optional<IT>> args){
    var ret= meet(m.sig().ret().get(), e.t());
    var improvedSig= m.sig().withTsT(args, ret);
    var omh= methodHeaderAnd(rcc, improvedSig.m().get(), improvedSig.rc(),(_,mi)->mi);
    assert omh.stream().allMatch(mh->assertNoBinderClash(rcc, mh));
    return omh
      .map(mh->headerResult(rcc,m,e,mh.sig(),improvedSig))
      .orElseGet(()->withImpl(rcc.c().ts(),m,improvedSig,e));
  }
  TSM headerResult(IT.RCC rcc, inference.M m, E e, core.Sig sig, M.Sig improvedSig){
    var rcc0= withTsNormBs(rcc,refineClsTsFromHeader(rcc, improvedSig,sig));
    return withImpl(dropMethBsFromClsTs(rcc0, improvedSig), m, normalizeSigAgainstHeader(rcc0, improvedSig), e);
  }
  private TSM withImpl(List<IT> ts, inference.M m, M.Sig sig, E e){
    var impl1= m.impl().get().withE(meet(e, sig.ret().get()));
    var noChange= sig.equals(m.sig()) && impl1 == m.impl().get();
    if (noChange){ return new TSM(ts, m); }
    return new TSM(ts, new inference.M(sig, Optional.of(impl1)));
  }
  private List<IT> refineClsTsFromHeader(IT.RCC rcc, M.Sig improvedSig, core.Sig imh){
    var Xs= B.xs(meths.from(rcc.c().name()).bs());
    var fromBody= meet(Streams.of(
      Streams.zip(imh.ts(), improvedSig.ts()).map((t,it)->refine(Xs,t,it)),
      Stream.of(refine(Xs,imh.ret(), improvedSig.ret()))).toList());
    return Streams.zip(rcc.c().ts(),fromBody).map(this::keepDecided).toList();
  }
  private IT keepDecided(IT decided, IT fromBody){
    var decidedIso= decided instanceof IT.RCX(var aRc, _) && aRc == RC.iso;
    var decidedSameX= xName(decided).isPresent() && xName(decided).equals(xName(fromBody)) && !decidedIso;
    if (decidedSameX){ return decided; }
    if (!(decided instanceof IT.RCC(var aRc, var aC, _) && fromBody instanceof IT.RCC b)){ return meet(decided, fromBody); }
    if (!aC.name().equals(b.c().name())){
      var asDecided= adaptedSuperTs(b, aC.name());
      return asDecided.isEmpty() ? decided : keepDecided(decided, asDecided.getFirst());
    }
    return b.withRCTs(aRc.or(b::rc), Streams.zip(aC.ts(),b.c().ts()).map(this::keepDecided).toList());
  }
  private List<IT> refine(List<String> Xs, core.T t,Optional<IT> it){ return refine(Xs,TypeRename.tToIT(t), it.get()); }
  private M.Sig normalizeSigAgainstHeader(IT.RCC rcc, M.Sig improvedSig){
    var targetBs= B.xs(improvedSig.bs().get());
    var h= methodHeader(rcc, improvedSig.m().get(), improvedSig.rc()).get();
    assert h.bsArity() == targetBs.size();
    var xs= MSigL.toXs(improvedSig.span(), targetBs);
    return improvedSig.withTsT(h.ps0().stream().map(p->Optional.of(h.inst(p, xs))).toList(), h.inst(h.ret0(), xs));
  }
  private List<IT> dropMethBsFromClsTs(IT.RCC rcc, M.Sig improvedSig){ return dropMethBs(rcc.c().ts(), B.xs(improvedSig.bs().get())); }
  List<IT> dropMethBs(List<IT> ts, List<String> methBs){
    if (methBs.isEmpty()){ return ts; }
    return ts.stream().map(t->dropMethBs(t, methBs)).toList();
  }
  IT dropMethBs(IT t, List<String> methBs){
    if (t instanceof IT.RCC rcc){ return withTsNormBs(rcc,dropMethBs(rcc.c().ts(), methBs)); }
    return xName(t).filter(methBs::contains).isPresent() ? IT.U.Instance : t;
  }
  private boolean assertNoBinderClash(IT.RCC rcc, core.M m){
    return Collections.disjoint(B.xs(meths.from(rcc.c().name()).bs()), B.xs(m.sig().bs()));
  }
  List<IT> refine(List<String> xs, IT t, IT t1){
    if (t1 instanceof IT.U){ return qMarks(xs.size()); }
    return switch (t){
      case IT.X x -> qMarks(xs.indexOf(x.name()), t1, xs.size());
      case IT.RCX(_, var x) -> refine(xs, x, stripRCAlsoThisSide(t1));
      case IT.ReadImmX(var x) -> refine(xs, x, t1 instanceof IT.ReadImmX(var x1) ? x1 : t1);
      case IT.RCC rcc -> propagateXs(xs, rcc, t1);
      case IT.U _ -> qMarks(xs.size()); //stripRCAlsoThisSide is needed to distinguish
    };//xs=[EE], t= imm EE, t1=imm ET -> [ET] | xs=[EE], t= EE, t1=imm ET ->[imm ET]
  }
  //xs=[EE], t= EE, t1=imm ET ->[imm ET]
  //xs=[EE], t= imm EE, t1=imm ET -> [ET]
  //xs=[EE], t= imm EE, t1=read Foo[Bar] -> [?? Foo[Bar]]
  //xs=[EE], t= imm EE, t1=ET -> [ET]//but only if ET only bound is ET:imm?
  static IT stripRCAlsoThisSide(IT t){ return switch (t){
    case IT.X x -> x;//IT.U.Instance;
    case IT.RCX(_, var x) -> x;
    case IT.ReadImmX(var x) -> x;
    case IT.RCC(_, var c, var span) -> new IT.RCC(Optional.empty(), c, span);
    case IT.U _ -> t;
  };}
  private boolean isASuperB(TName a, TName b){
    var d= meths._from(b);
    if (d == null){ return false; } // {..}.foo etc.
    return LiteralDeclarations.has(d.cs(),a);
  }
  private List<IT.RCC> adaptedSuperTs(IT.RCC src, TName target){
    var d= meths._from(src.c().name());
    if (d == null){ return List.of(); } // {..}.foo etc.
    var xs= B.xs(d.bs());
    return d.cs().stream()
      .filter(sc->sc.name().equals(target))
      .distinct()
      .map(ci->new IT.RCC(src.rc(), TypeRename.tcToITC(ci),src.span()))
      .map(rcc->(IT.RCC)TypeRename.of(rcc, xs, src.c().ts()))
      .toList();
  }
  List<IT> propagateXs(List<String> xs, IT.RCC r, IT t1){
    if (!(t1 instanceof IT.RCC cc)){ return qMarks(xs.size()); }
    var c= r.c();
    if (!cc.c().name().equals(c.name())){
      var supOk= adaptedSuperTs(cc,c.name());
      if (!supOk.isEmpty()){ return propagateXs(xs,r,supOk.getFirst()); }
      var subOk= adaptedSuperTs(r,cc.c().name());
      if (!subOk.isEmpty()){ return propagateXs(xs,subOk.getFirst(),t1); }
      return qMarks(xs.size());
    }
    var res= Streams.zip(c.ts(), cc.c().ts()).map((t,ti)->refineArg(xs, t, ti)).toList();
    return res.isEmpty() ? qMarks(xs.size()) : meet(res);
  }
  private List<IT> refineArg(List<String> xs, IT t, IT t1){
    var otherHead= t instanceof IT.RCC r && !(t1 instanceof IT.RCC cc && cc.c().name().equals(r.c().name()));
    return otherHead ? qMarks(xs.size()) : refine(xs, t, t1);
  }
  static <TT> List<TT> norm(List<TT> original, List<TT> candidate){
    if (candidate == original){ return original; }
    assert candidate.size() == original.size();
    for (int i : Range.of(original)){
      if (candidate.get(i) != original.get(i)){
        assert !(candidate.get(i) instanceof E || candidate.get(i) instanceof M) || !candidate.get(i).equals(original.get(i));
        return candidate;
      }
    }
    return original;
  }
  private static boolean needsPrototypeAscription(E.Literal l){
    var headKnown= l.infHead() || !l.infName() || !l.cs().isEmpty();
    if (headKnown){ return false; }
    return (l.t() instanceof IT.U /*&& l.ms().stream().anyMatch(m-> !m.sig().isFull())*/);
  }
  private E prototypeAscribeRootReceiver(E arg, IT expected, boolean receiver){
    if (!(expected instanceof IT.RCC exp)){ return arg; }
    return switch (arg){
      case E.Call c -> c.withE(prototypeAscribeRootReceiver(c.e(), expected, true));
      case E.ICall c -> c.withE(prototypeAscribeRootReceiver(c.e(), expected, true));
      case E.Literal l when !needsPrototypeAscription(l) -> arg;
      case E.Literal l when !receiver || implementable(exp.c().name()) -> l.withT(prototypeHead(exp,l.span()));
      case E.Literal l -> itself(l);
      default -> arg;
    };
  }
  private boolean implementable(TName head){
    var d= meths._from(head);
    if (d == null){ return false; }
    var foreign= !head.pkgName().equals(meths.p().name());
    var foreignForbidden= foreign && (!head.isPublic() || LiteralDeclarations.has(d.cs(),LiteralDeclarations.sealed));
    return !foreignForbidden && TypeSystem.hasInstance(d);
  }
  private E.Literal itself(E.Literal l){
    var res= new E.Literal(Optional.of(RC.imm), l.name(), l.bs(), l.cs(), l.thisName(), l.ms(), l.src(), true);
    return res.withT(preciseSelf(res).get());
  }
  private IT.RCC prototypeHead(IT.RCC expected, TSpan span){
    return new IT.RCC(expected.rc(), new IT.C(expected.c().name(), qMarks(expected.c().ts().size())), span);
  }

  private static IT normToBound(IT t, EnumSet<RC> allowed){
    if (allowed.size() == 1){ return t.withRC(allowed.iterator().next()); }
    if (!(t instanceof IT.RCC(var rc, var c, var span))){ return t; }
    var open= rc.isEmpty() || rc.get() == RC.iso && !allowed.contains(RC.iso);
    if (!open){ return t; }
    return new IT.RCC(allowed.contains(RC.imm) ? Optional.empty() : Optional.of(RC.read), c, span);
  }
  static List<IT> normToBounds(List<B> bs, List<IT> ts){
    return Streams.zip(ts,bs).map((ti,bi)->normToBound(ti,bi.rcs())).toList();
  }
  private static List<IT> normToBounds(List<B> scope, List<B> bs, List<IT> ts){
    return Streams.zip(ts,bs).map((ti,bi)->normToBound(scope,ti,bi.rcs())).toList();
  }
  private static IT normToBound(List<B> scope, IT t, EnumSet<RC> allowed){
    var sameType= xName(t).map(x->B.get(scope,x).rcs().equals(allowed)).orElse(true);
    return sameType ? normToBound(t,allowed) : t;
  }
  private static Optional<String> xName(IT t){ return switch (t){
    case IT.X x -> Optional.of(x.name());
    case IT.RCX(_, var x) -> Optional.of(x.name());
    case IT.ReadImmX(var x) -> Optional.of(x.name());
    default -> Optional.empty();
  };}
  private IT.RCC withTsNormBs(IT.RCC rcc, List<IT> ts){
    var d= meths._from(rcc.c().name());
    if (d == null){ return rcc.withTs(ts); }   // {..}.foo etc.
    return rcc.withTs(normToBounds(d.bs(), ts));
  }
}

record MSigL(RC rc, List<String> xs, List<B> clsBs, List<IT> clsArgs, List<B> methBs, List<IT> ps0, IT ret0){
  int nCls(){ return clsArgs.size(); }
  int bsArity(){ return methBs.size(); }

  IT ret(List<IT> targs){ return inst(ret0, targs); }

  MSigL withClsArgs(List<IT> clsArgs){
    assert clsArgs.size() == this.clsArgs.size();
    return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0);
  }

  IT inst(IT t, List<IT> targs){//Note: this will eventually become an error at type system time.
    targs= fixTargs(targs, bsArity());
    var ts= Push.of(clsArgs,targs);//performance? we could cache this result since targs is fixed and used over and over
    return TypeRename.of(t, xs, ts);
  }
  static List<IT> fixTargs(List<IT> targs, int n){
    var k= targs.size();
    if (k > n){ return targs.subList(0, n); }
    return Push.of(targs, InjectionSteps.qMarks(n-k));
  }
  static List<IT> toXs(TSpan span,List<String> targetBs){ return targetBs.stream().<IT>map(n->new IT.X(n,span)).toList(); }
}