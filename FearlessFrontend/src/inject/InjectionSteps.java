package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.Optional;
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

public record InjectionSteps(Methods meths, int cap){
  public static List<core.E.Literal> steps(Methods meths, List<E.Literal> tops){
    var s= new InjectionSteps(meths, deepest(meths));
    assert tops.stream().allMatch(l -> l.thisName().equals("this"));
    //No! at this point they have been (correctly) divided in layers assert tops.stream().sorted().toList().equals(tops);
    return tops.stream()
      .map(l -> s.stepDec(meths.cache().get(l.name()), l)).toList();
  }
  private static int deepest(Methods meths){
    var ds= Stream.concat(meths.cache().values().stream(), meths.other().dom().stream().map(meths::from));
    return ds.flatMapToInt(InjectionSteps::depths).max().orElse(1);
  }
  private static IntStream depths(core.E.Literal d){
    var cs= d.cs().stream().mapToInt(c -> TypeRename.tcToITC(c).depth());
    var ms= d.ms().stream().flatMap(m -> Push.of(m.sig().ts(), m.sig().ret()).stream()).mapToInt(t -> TypeRename.tToIT(t).depth());
    return IntStream.concat(cs, ms);
  }
  private static int size(IT t){ return t instanceof IT.RCC rcc ? size(rcc.c()) : 1; }
  private static int size(IT.C c){ return 1+c.ts().stream().mapToInt(InjectionSteps::size).sum(); }
  private static int size(M m){
    var ts= Push.of(m.sig().ts(), m.sig().ret()).stream().mapToInt(t -> t.map(InjectionSteps::size).orElse(1)).sum();
    return ts+m.impl().map(i -> size(i.e())).orElse(0);
  }
  private static int size(E e){ return size(e.t())+switch (e){
    case E.X _ -> 0;
    case E.Type t -> size(t.type());
    case E.Call c -> size(c.e())+c.targs().stream().mapToInt(InjectionSteps::size).sum()+c.es().stream().mapToInt(InjectionSteps::size).sum();
    case E.Literal l -> l.cs().stream().mapToInt(InjectionSteps::size).sum()+l.ms().stream().mapToInt(InjectionSteps::size).sum();
  };}
  private core.E.Literal stepDec(core.E.Literal di, E.Literal li){ return di.withMs(li.ms().stream().map(m -> stepDecM(di, m)).toList()); }
  private boolean sameM(core.Sig s1, M.Sig s2){
    return s1.m().equals(s2.m().get()) && s1.rc() == s2.rc().orElse(RC.imm);
  }
  private core.M stepDecM(core.E.Literal di, M m){
    var mCore= OneOr.of("Method mismatch", di.ms().stream().filter(mi -> sameM(mi.sig(), m.sig())));
    if (m.impl().isEmpty()){ return mCore; }//assert same type as m lifted to core
    var e= m.impl().get().e();
    var span= di.name().approxSpan();
    var xs= m.impl().get().xs();
    var thisRc= LiteralDeclarations.has(di.cs(), LiteralDeclarations.captureFree) ? RC.imm : mCore.sig().rc();
    var thisType= new IT.RCC(Optional.of(thisRc), new IT.C(di.name(), MSigL.toXs(span, B.xs(di.bs()))), span);//no preferred on self names
    var ei= meet(e, TypeRename.tToIT(mCore.sig().ret()));
    var g= Gamma.of(xs, TypeRename.tToIT(mCore.sig().ts()), di.thisName(), thisType);
    var bs= Push.of(di.bs(), m.sig().bs().get());
    ei = new InjectionSteps(meths, cap*size(ei)).nextStar(bs, g, ei);
    return new core.M(mCore.sig(), xs, Optional.of(new ToCore(bs, meths).of(ei, e)));
  }
  E meet(E e, IT t){
    if (e instanceof E.Type tt){ return nextT(tt); }
    var typedLit= e instanceof E.Literal l && l.t().isTV();
    if (typedLit){ return e; }
    e = prototypeAscribeRootReceiver(e, t, Optional.empty());
    return e.withT(meet(e.t(), t));
  }
  private IT belowOrDecided(RCC x1, RCC x2){
    var s1= _below(x1, x2);
    if (s1 != null){ return s1.isTV() || !x2.isTV() ? s1 : x2; }
    var s2= _below(x2, x1);
    if (s2 != null){ return s2.isTV() || !x1.isTV() ? s2 : x1; }
    return x1;
  }
  private IT _below(RCC sub, RCC sup){
    var d= meths._from(sub.c().name());
    if (d == null){ return null; }
    var patterns= d.cs().stream().filter(c -> c.name().equals(sup.c().name())).toList();
    if (patterns.isEmpty()){ return null; }
    var xs= B.xs(d.bs());
    var refined= meet(patterns.stream().map(c -> refine(xs, new IT.RCC(Optional.empty(), TypeRename.tcToITC(c), sub.span()), sup)).toList());
    return sub.withRCTs(meetRcNoH(sub.rc(), sup.rc()), meet(sub.c().ts(), refined));
  }
  IT meet(IT t1, IT t2){
    if (t2.undecided()){ return t1 instanceof IT.U ? t2 : t1; }
    if (t1.undecided()){ return t2; }
    if (t1.equals(t2)){ return t1; }
    var t1ReadImmOfT2= t1 instanceof IT.ReadImmX(var x1) && x1.equals(t2);
    if (t1ReadImmOfT2){ return t1; }
    var t2ReadImmOfT1= t2 instanceof IT.ReadImmX(var x2) && x2.equals(t1);
    if (t2ReadImmOfT1){ return t2; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.c().name().equals(x2.c().name())){ return belowOrDecided(x1, x2); }
      var rc= meetRcNoH(x1.rc(), x2.rc());
      return x1.withRCTs(rc, meet(x1.c().ts(), x2.c().ts()));
    }
    if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX(var rc2, var x2)) || !x1.x().equals(x2)){ return t1; }
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
  IT join(IT t1, IT t2){
    if (t2 instanceof IT.U){ return t1; }
    if (t1 instanceof IT.U){ return t2; }
    if (t1.equals(t2)){ return t1; }
    var cands= Push.of(candidates(t1), candidates(t2));
    for (var top : cands){ var res= _aboveAll(top, cands); if (res != null){ return res; } }
    var common= _commonSupertype(cands);
    return common == null ? new IT.Amb(cands) : _aboveAll(common, cands);
  }
  private IT _commonSupertype(List<IT> cands){
    var minimal= meths.commonSuperHeads(cands);
    if (minimal.size() != 1){ return null; }
    return adaptedSuperTs((IT.RCC)cands.getFirst(), minimal.getFirst()).getFirst();
  }
  private static List<IT> candidates(IT t){ return t instanceof IT.Amb(var cs) ? cs : List.of(t); }
  private IT _aboveAll(IT top, List<IT> cands){
    IT res= top;
    for (var c : cands){
      var up= _liftTo(c, top);
      if (up == null){ return null; }
      res = sameShapeJoin(res, up);
    }
    return res;
  }
  private IT _liftTo(IT c, IT top){
    if (c instanceof IT.RCC rc && top instanceof IT.RCC rt){
      if (rc.c().name().equals(rt.c().name())){ return c; }
      var up= adaptedSuperTs(rc, rt.c().name());
      return up.isEmpty() ? null : up.getFirst();
    }
    var sameX= xName(c).isPresent() && xName(c).equals(xName(top));
    return sameX ? c : null;
  }
  private IT sameShapeJoin(IT a, IT b){
    if (a instanceof IT.RCC x1 && b instanceof IT.RCC x2){ return x1.withRCTs(joinRcNoH(x1.rc(), x2.rc()), meet(x1.c().ts(), x2.c().ts())); }
    if (a instanceof IT.RCX x1 && b instanceof IT.RCX x2){ return x1.withRC(joinRcNoH(Optional.of(x1.rc()), Optional.of(x2.rc())).get()); }
    return meet(a, b);
  }
  static Optional<RC> joinRcNoH(Optional<RC> a, Optional<RC> b){
    if (a.isEmpty()){ return b; }
    if (b.isEmpty()){ return a; }
    var x= noH(a.get());
    var y= noH(b.get());
    if (x == y || y == RC.iso){ return Optional.of(x); }
    if (x == RC.iso){ return Optional.of(y); }
    return Optional.of(RC.read);
  }
  List<IT> join(List<IT> t1, List<IT> t2){ return Streams.zip(t1, t2).map(this::join).toList(); }
  List<IT> join(List<List<IT>> tss){ return tss.stream().reduce(this::join).get(); }
  List<IT> meet(List<IT> t1, List<IT> t2){ return Streams.zip(t1, t2).map(this::meet).toList(); }
  List<IT> meet(List<List<IT>> tss){ return tss.stream().reduce(this::meet).get(); }
  E nextStar(List<B> bs, Gamma g, E e){
    var start= e;
    if (e.done(g)){ return e; }
    var grew= 0;
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
      grew = oe.t().depth() > e.t().depth() ? grew+1 : 0;
      var forever= grew == 50 || oe.t().depth() > cap;
      if (forever){ throw meths.p().err().typeGrowsForever(oe); }
      e = oe;
    }
  }
  private List<E> nextStar(List<B> bs, Gamma g, List<E> es){
    return norm(es, es.stream().map(ei -> nextStar(bs, g, ei)).toList());
  }
  private List<E> meetWithTargs(List<E> originEs, List<E> es, MSigL m, List<IT> targs){
    var res= norm(es, Streams.zip(es, m.ps0()).map((e,p) -> meet(e, m.inst(p, targs))).toList());
    assert notBackToOrigin(originEs, res);
    return res;
  }
  private boolean notBackToOrigin(List<E> originEs, List<E> res){
    //complex but invaluable: if it fails it means we are going 'back and forth'
    //and this could cause loops.
    return Streams.zip(res, originEs).allMatch((r,o) -> r == o || !r.equals(o));
  }
  E next(List<B> bs, Gamma g, E e){
    //assert meet(e.t(),res.t()).equals(res.t()): e.t()+" "+res.t();// Does not hold. How can it be?
    return switch (e){
      case E.X x -> nextX(g, x);
      case E.Literal l -> nextL(bs, g, l);
      case E.Call c -> nextC(bs, g, c);
      case E.Type c -> nextT(c);
    };
  }
  private IT preferred(IT.RCC type){
    var d= meths.from(type.c().name());//d.cs() does contain all the transitive supertypes already.
    var c= OneOr.opt("Repeated WidenTo supertype", d.cs().stream().filter(ci -> ci.name().equals(LiteralDeclarations.widen)));
    if (c.isEmpty()){ return type; }
    var wid= TypeRename.of(TypeRename.tToIT(OneOr.of("WidenTo has one type argument", c.get().ts().stream())), B.xs(d.bs()), type.c().ts());
    if (!(wid instanceof IT.RCC(_, var widC, _))){ return type; }
    return new IT.RCC(type.rc(), widC, type.span());
  }
  private RC overloadNorm(Optional<RC> rc){ return rc.map(r -> r == RC.iso ? RC.imm : noH(r)).orElse(RC.imm); }
  private Optional<core.M> oneFromGuessRC(List<core.M> ms, RC rc){
    if (ms.size() == 1){ return Optional.of(ms.getFirst()); }
    var readOne= OneOr.opt("Not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.read));
    var mutOne= OneOr.opt("Not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.mut));
    var immOne= OneOr.opt("Not well formed ms", ms.stream().filter(m -> m.sig().rc() == RC.imm));
    if (rc == RC.read){ return readOne.or(() -> immOne).or(() -> mutOne); }
    if (rc == RC.mut){ return mutOne.or(() -> readOne).or(() -> immOne); }
    assert rc == RC.imm;
    return immOne.or(() -> readOne).or(() -> mutOne);
  }
  private Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite, RC guess){
    var d= meths._from(rcc.c().name());
    if (d == null){ return Optional.empty(); }//case {..}.foo
    var ms= d.ms().stream().filter(m -> m.sig().m().equals(name));
    var om= favorite
      .map(rc -> OneOr.opt("Ambiguous method header for explicit RC", ms.filter(mi -> mi.sig().rc() == rc)))
      .orElseGet(() -> oneFromGuessRC(ms.toList(), guess));
    return om.map(mm -> methodHeaderInstance(rcc, d, mm));
  }
  private MSigL methodHeaderInstance(IT.RCC rcc, core.E.Literal d, core.M m){
    var clsXs= B.xs(d.bs());
    assert Set.copyOf(clsXs).size() == clsXs.size();
    var methXs= B.xs(m.sig().bs());
    assert Set.copyOf(methXs).size() == methXs.size();
    assert Collections.disjoint(clsXs, methXs);
    var clsArgs= rcc.c().ts();
    assert clsArgs.size() == clsXs.size();
    var xs= Push.of(clsXs, methXs);//TODO: could avoid materializing the two lists
    var ps0= TypeRename.tToIT(m.sig().ts());
    var ret0= TypeRename.tToIT(m.sig().ret());
    return new MSigL(m.sig().rc(), xs, d.bs(), clsArgs, m.sig().bs(), ps0, ret0);
  }
  Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){
    return methodHeader(rcc, name, favorite, overloadNorm(rcc.rc()));
  }
  static List<IT> qMarks(int n){ return Stream.<IT>generate(() -> IT.U.Instance).limit(n).toList(); }
  private List<IT> qMarks(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i -> i == n ? t : IT.U.Instance).toList(); }
  private E nextX(Gamma g, E.X x){
    var t1Base= g.get(x.name());
    var notIn= g.notFunnelledInto(x.name());
    if (notIn.isPresent()){ throw meths.p().err().captureNotFunnelled(x, t1Base, notIn.get()); }
    var t1= g.getWithRC(x.name());
    var t2= x.t();
    if (t1.equals(t2)){ return x; }
    if (!t2.undecided()){ updateG(g, x.name(), t1Base, t2); }
    return x.withT(meet(t1, t2));
  }
  private void updateG(Gamma g, String x, IT t1, IT t2){
    if (t1.undecided()){ g.update(x, t2); return; }
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
    a = noH(a); b = noH(b);
    if (a == b){ return a; }
    if (a == RC.read){ return b; }
    if (b == RC.read){ return a; }
    return RC.iso;
  }
  private E nextT(E.Type t){
    if (!t.t().undecided()){ return t; }
    return t.withT(preferred(t.type()));
  }
  private E nextC(List<B> bs, Gamma g, E.Call c){
    var e= nextStar(bs, g, c.e());
    if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    var guess= overloadNorm(rcc.rc().map(rc -> rc == RC.iso ? c.t().explicitRC().orElse(rc) : rc));
    var om= methodHeader(rcc, c.name(), c.rc(), guess);
    if (om.isEmpty()){ return c.withEEs(e, nextStar(bs, g, c.es())); }
    var m= om.get();
    assert m.ps0().size() == c.es().size();
    var all= decidedThen(c, m).stream().map(t -> deFresh(g, t)).toList();
    assert all.size() == m.nCls()+m.bsArity();
    var clsTs= normToBounds(bs, m.clsBs(), all.subList(0, m.nCls()));
    var targs= normToBounds(bs, m.methBs(), all.subList(m.nCls(), all.size()));
    e = meet(e, rcc.withTs(clsTs));
    m = m.withClsArgs(clsTs);
    var it= meet(c.t(), m.ret(targs));
    var es1= nextStar(bs, g, meetWithTargs(c.es(), c.es(), m, targs));
    var noChange= e == c.e() && es1 == c.es() && targs.equals(c.targs()) && it.equals(c.t());
    if (noChange){ return c; }
    return c.withMore(e, c.rc().orElse(m.rc()), targs, es1, it);
  }
  private List<IT> fromArgs(MSigL m, List<E> es, boolean onlyLiterals){
    var n= m.nCls()+m.bsArity();
    var lower= Streams.zip(m.ps0(), es).filter((p,e) -> !(p instanceof IT.RCC) && (!onlyLiterals || e instanceof E.Literal)).map((p,e) -> refine(m.xs(), p, e.t()));
    var exact= Streams.zip(m.ps0(), es).filter((p,e) -> p instanceof IT.RCC && (!onlyLiterals || e instanceof E.Literal)).map((p,e) -> refine(m.xs(), p, e.t()));
    return meet(Streams.of(Stream.of(join(Streams.of(Stream.of(qMarks(n)), lower).toList())), exact).toList());
  }
  private static IT deFresh(Gamma g, IT t){
    if (!(t instanceof IT.RCC rcc)){ return t; }
    var o= g._owner(rcc.c().name());
    var head= o != null && o.infName() && o.t() instanceof IT.RCC h && !h.c().name().equals(o.name()) ? h.c() : rcc.c();
    return new IT.RCC(rcc.rc(), head, rcc.span()).withTs(head.ts().stream().map(ti -> deFresh(g, ti)).toList());
  }
  private List<IT> decidedThen(E.Call c, MSigL m){
    var targs= MSigL.fixTargs(c.targs(), m.bsArity());
    var args= fromArgs(m, c.es(), false);
    var fromRet= refine(m.xs(), m.ret0(), c.t());
    var all= meet(List.of(Push.of(m.clsArgs(), targs), args, fromRet));
    var written= Push.of(m.clsArgs(), writtenTargs(c) ? targs : qMarks(m.bsArity()));
    var hard= fromArgs(m, c.es(), true);
    var exactRet= m.ret0() instanceof IT.RCC ? fromRet : qMarks(fromRet.size());
    var exact= Streams.zip(written, exactRet).map((w,r) -> decided(w) ? w : r).toList();
    var fixed= Streams.zip(exact, hard).map((f,h) -> decided(f) ? f : h).toList();
    return Streams.zip(fixed, all).map((b,r) -> decided(b) ? b : r).toList();
  }
  static boolean writtenTargs(E.Call c){ return c.src().inner instanceof fearlessFullGrammar.E.Call sc && sc.targs().isPresent(); }
  private static boolean decided(IT t){ return t.isTV() && !(t instanceof IT.RCC(var rc, _, _) && rc.isEmpty()); }
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    var selfUnknown= l.infName() && l.rc().isEmpty();
    if (selfUnknown){ return Optional.empty(); }
    var span= l.name().approxSpan();
    return Optional.of(new IT.RCC(l.rc(), new IT.C(l.name(), MSigL.toXs(span, B.xs(l.bs()))), span));
  }
  private Optional<IT.RCC> superSelf(E.Literal l, Optional<IT.RCC> precise){
    if (l.cs().size() != 1){ return precise; }
    return precise.map(p -> new IT.RCC(p.rc(), l.cs().getFirst(), p.span()));
  }
  private E nextL(List<B> bs, Gamma g, E.Literal l){
    var infHead= l.infHead();//infHead is set in l.withCsMs and l.withMsT
    // to mean the HEAD is inferred as IT.RCC and has already been used to expand methods
    var selfPrecise= preciseSelf(l);
    var selfSuper= superSelf(l, selfPrecise);
    if (!infHead){
      l = l.infName() ? selfSuper.map(l::withT).orElse(l) : l.withT(selfPrecise.get());
      if (!(l.t() instanceof IT.RCC(_, var c, _))){ return l; }//!infHead after passing this test means right now we can expand methods
      var anon= l.infName() && !c.name().equals(l.name());
      if (anon && l.ms().isEmpty() && l.t().isTV() && meths._from(c.name()) != null){ return literalAsType(l, (IT.RCC)l.t()); }
      var o= anon ? g._owner(c.name()) : null;
      if (o != null && o.infName()){ throw meths.p().err().implementsAnonymousType(l, o); }
      l = anon ? meths.expandLiteral(l, c, bs) : meths.expandDeclaration(l, true);
    }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    var res= new ArrayList<M>(l.ms().size());
    var rcci= withTsNormBs(rcc, rcc.c().ts());
    var exact= rcc.c().ts();
    var lower= qMarks(exact.size());
    for (var mi : l.ms()){
      assert mi.impl().isEmpty() || selfPrecise.isEmpty() || rcc.isTV();
      var next= mi.impl().isEmpty() ? header(rcci, mi) : nextMStarOp(bs, g, l, selfPrecise, rcci, mi);
      assert next.m == mi || !next.m.equals(mi);
      exact = meet(exact, next.ts);
      lower = join(lower, next.lower);
      res.add(next.m);
    }
    var ts= orLower(exact, lower).stream().map(t -> deFresh(g, t)).toList();
    var ms= norm(l.ms(), Collections.unmodifiableList(res));
    var noChange= ms == l.ms() && ts.equals(rcc.c().ts());
    if (noChange){ return commitToTable(g, bs, l, rcc); }
    var t= withTsNormBs(rcc, ts);
    return commitToTable(g, bs, l.withMsT(ms, t), t);
  }
  private E commitToTable(Gamma g, List<B> bs, E.Literal l, IT.RCC rcc){
    var name= l.name();
    var notReady= !rcc.isTV() || hasU(l.ms()) || meths.cache().containsKey(name);
    if (notReady){ return l; }
    var freeNames= Streams.of(new FreeXs(g).ftvMs(l.ms()), new FreeXs(g).ftvCs(l.cs()), rcc.ftv());
    var localBs= freeNames.distinct().map(x -> B.get(bs, x)).toList();
    var newName= name.withArity(localBs.size());
    var ms= fixArity(l.ms(), name, newName);
    var orc= l.rc().or(rcc::rc).map(InjectionSteps::noH);
    assert l.infName();
    assert l.bs().isEmpty();
    var noMeth= l.ms().stream().allMatch(m -> m.impl().isEmpty());
    var selfInferred= rcc.c().name().equals(l.name());
    if (noMeth && !selfInferred && meths._from(rcc.c().name()) != null){ return literalAsType(l, rcc); }
    var head= rcc.c().name();
    var foreignPrivate= !selfInferred && !head.isPublic() && !head.pkgName().equals(meths.p().name());
    if (foreignPrivate){ throw meths.p().err().extendedForeign(l, head, "private"); }
    var cs= ToCore.distinctTypes(localBs, selfInferred ? meths.implied(rcc.c()) : Push.of(rcc.c(), meths.implied(rcc.c())));
    assert l.infHead();
    l = new E.Literal(orc, newName, localBs, cs, l.thisName(), ms, rcc, l.src(), l.infName(), l.infHead(), l.g());
    meths.checkMagicSupertypes(l, cs);
    if (selfInferred){ l = l.withT(preciseSelf(l).get()); }
    assert !meths.cache().containsKey(name);
    meths.register(l);
    g.tableGrew();
    return l;
  }
  private E.Type literalAsType(E.Literal l, IT.RCC rcc){
    if (!l.thisName().equals("_")){ throw meths.p().err().selfNameDeadCode(l); }
    var head= rcc.c().name();
    var foreignPrivate= !head.isPublic() && !head.pkgName().equals(meths.p().name());
    if (foreignPrivate){ throw meths.p().err().extendedForeign(l, head, "private"); }
    var orcc= new IT.RCC(l.rc().or(rcc::rc).map(InjectionSteps::noH), rcc.c(), rcc.span());
    return new E.Type(orcc, preferred(orcc), l.src(), l.g());
  }
  private List<M> fixArity(List<M> ms, TName name, TName newName){
    if (name.equals(newName)){ return ms; }
    return norm(ms, ms.stream().map(mi -> fixArity(mi, name, newName)).toList());
  }
  private M fixArity(M m, TName name, TName newName){
    var s= m.sig();
    if (!s.origin().get().equals(name)){ return m; }
    return m.withSig(s.withOrigin(newName));
  }
  private static boolean hasU(List<M> ms){
    return !ms.stream()
      .allMatch(m -> m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t -> t.get().isTV()));
  }
  private List<Optional<IT>> updateArgs(M m, Gamma g){
    return Streams.zip(m.impl().get().xs(), m.sig().ts()).map((x,oi) -> x.equals("_") ? oi : Optional.of(meet(oi.get(), g.get(x)))).toList();
  }
  record TSM(List<IT> ts, List<IT> lower, M m){
    TSM(List<IT> ts, M m){ this(ts, qMarks(ts.size()), m); }
  }
  private record Refined(List<IT> exact, List<IT> lower){}
  private static List<IT> orLower(List<IT> exact, List<IT> lower){ return Streams.zip(exact, lower).map((x,lo) -> x instanceof IT.U ? lo : x).toList(); }
  TSM nextMStarOp(List<B> bs, Gamma g, E.Literal l, Optional<IT.RCC> selfPrecise, IT.RCC rcc, M m){
    assert m.impl().isPresent();
    var litBs= l.infName() ? bs : l.bs();
    g.newScope(m.sig().rc().get(), litBs, l);
    g.declare(l.thisName(), selfPrecise.<IT>map(s -> new IT.RCC(s.rc().map(RC::isoToMut), s.c(), s.span())).orElse(IT.U.Instance));
    g.newScope(m.sig().rc().get(), litBs, l);
    assert m.sig().m().get().arity() == m.impl().get().xs().size();
    Streams.zip(m.impl().get().xs(), m.sig().ts()).forEach((x,t) -> g.declare(x, t.get()));
    var e= nextStar(Push.of(litBs, m.sig().bs().get()), g, meet(m.impl().get().e(), m.sig().ret().get()));
    var args= updateArgs(m, g);
    g.popScope();
    g.popScope();
  /*The meet below narrows a method's return type to the type of its body, so a literal only ever
  gets more precise than what the use site asked for. What keeps that from destroying an invariant
  instantiation is that a decided type argument is never re-decided: meetWithTargs in nextC and the meet in
  nextMStarOp push what is already known down before a body is inferred, and keepDecided then only
  fills the type arguments still unknown. See the five tests named in TypeSystemTest, next to
  blockLetInfersItsTypeFromTheLambdaBody, for what base needs the meet itself for.*/
    var ret= meet(m.sig().ret().get(), e.t());
    var h= header(rcc, m.withSig(m.sig().withTsT(args, ret)));
    var impl= m.impl().get().withE(meet(e, h.m().sig().ret().get()));
    var noChange= h.m().sig().equals(m.sig()) && impl == m.impl().get();
    return new TSM(h.ts(), h.lower(), noChange ? m : new M(h.m().sig(), Optional.of(impl)));
  }
  private TSM header(IT.RCC rcc, M m){
    var sig= m.sig();
    var oh= methodHeader(rcc, sig.m().get(), sig.rc());
    if (oh.isEmpty()){ return new TSM(rcc.c().ts(), m); }
    var r= refineClsTsFromHeader(rcc, sig, oh.get());
    var h= oh.get().withClsArgs(withTsNormBs(rcc, orLower(r.exact(), r.lower())).c().ts());
    var methXs= B.xs(sig.bs().get());
    assert h.bsArity() == methXs.size();
    var xs= MSigL.toXs(sig.span(), methXs);
    var norm= sig.withTsT(h.ps0().stream().map(p -> Optional.of(h.inst(p, xs))).toList(), h.inst(h.ret0(), xs));
    return new TSM(dropMethBs(withTsNormBs(rcc, r.exact()).c().ts(), methXs), dropMethBs(r.lower(), methXs), m.withSig(norm));
  }
  private Refined refineClsTsFromHeader(IT.RCC rcc, M.Sig improvedSig, MSigL h){
    var Xs= B.xs(h.clsBs());
    var bareRet= !(h.ret0() instanceof IT.RCC);
    var fromRet= refine(Xs, h.ret0(), improvedSig.ret().get());
    var lower= Streams.zip(rcc.c().ts(), fromRet).map((d,f) -> bareRet && d instanceof IT.U ? f : IT.U.Instance).toList();
    var exactRet= Streams.zip(rcc.c().ts(), fromRet).map((d,f) -> bareRet && d instanceof IT.U ? IT.U.Instance : f).toList();
    var fromBody= meet(Streams.of(
      Streams.zip(h.ps0(), improvedSig.ts()).map((t,it) -> refine(Xs, t, it.get())),
      Stream.of(exactRet)).toList());
    return new Refined(Streams.zip(rcc.c().ts(), fromBody).map(this::keepDecided).toList(), lower);
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
    return b.withRCTs(aRc.or(b::rc), Streams.zip(aC.ts(), b.c().ts()).map(this::keepDecided).toList());
  }
  List<IT> dropMethBs(List<IT> ts, List<String> methBs){
    if (methBs.isEmpty()){ return ts; }
    return ts.stream().map(t -> dropMethBs(t, methBs)).toList();
  }
  IT dropMethBs(IT t, List<String> methBs){
    if (t instanceof IT.RCC rcc){ return withTsNormBs(rcc, dropMethBs(rcc.c().ts(), methBs)); }
    return xName(t).filter(methBs::contains).isPresent() ? IT.U.Instance : t;
  }
  List<IT> refine(List<String> xs, IT t, IT t1){
    if (t1.undecided()){ return qMarks(xs.size()); }
    return switch (t){
      case IT.X x -> qMarks(xs.indexOf(x.name()), t1, xs.size());
      case IT.RCX(_, var x) -> refine(xs, x, stripRCAlsoThisSide(t1));
      case IT.ReadImmX(var x) -> refine(xs, x, t1 instanceof IT.ReadImmX(var x1) ? x1 : t1);
      case IT.RCC rcc -> propagateXs(xs, rcc, t1);
      case IT.U _, IT.Amb _ -> qMarks(xs.size()); //stripRCAlsoThisSide is needed to distinguish
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
    case IT.U _, IT.Amb _ -> t;
  };}
  private List<IT.RCC> adaptedSuperTs(IT.RCC src, TName target){
    return meths.implied(src.c()).stream().filter(c -> c.name().equals(target)).map(c -> new IT.RCC(src.rc(), c, src.span())).toList();
  }
  List<IT> propagateXs(List<String> xs, IT.RCC r, IT t1){
    if (!(t1 instanceof IT.RCC cc)){ return qMarks(xs.size()); }
    var c= r.c();
    if (!cc.c().name().equals(c.name())){
      var supOk= adaptedSuperTs(cc, c.name());
      if (!supOk.isEmpty()){ return propagateXs(xs, r, supOk.getFirst()); }
      var subOk= adaptedSuperTs(r, cc.c().name());
      if (!subOk.isEmpty()){ return propagateXs(xs, subOk.getFirst(), t1); }
      return qMarks(xs.size());
    }
    var res= Streams.zip(c.ts(), cc.c().ts()).map((t,ti) -> refineArg(xs, t, ti)).toList();
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
    return l.t().undecided();
  }
  private E prototypeAscribeRootReceiver(E arg, IT expected, Optional<MName> called){
    if (!(expected instanceof IT.RCC exp)){ return arg; }
    return switch (arg){
      case E.Call c -> c.withEEs(prototypeAscribeRootReceiver(c.e(), expected, Optional.of(c.name())), c.es());
      case E.Literal l when !needsPrototypeAscription(l) -> arg;
      case E.Literal l when called.map(name -> implementable(exp.c().name()) && !declares(l, name)).orElse(true) -> l.withT(prototypeHead(exp, l.span()));
      case E.Literal l -> itself(l);
      default -> arg;
    };
  }
  private static boolean declares(E.Literal l, MName name){
    return l.ms().stream().map(M::sig).anyMatch(s -> s.m().equals(Optional.of(name)) && s.ret().isPresent() && s.ts().stream().allMatch(Optional::isPresent));
  }
  private boolean implementable(TName head){
    var d= meths._from(head);
    if (d == null){ return false; }
    var foreign= !head.pkgName().equals(meths.p().name());
    var foreignForbidden= foreign && (!head.isPublic() || LiteralDeclarations.has(d.cs(), LiteralDeclarations.sealed));
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
    return Streams.zip(ts, bs).map((ti,bi) -> normToBound(ti, bi.rcs())).toList();
  }
  private static List<IT> normToBounds(List<B> scope, List<B> bs, List<IT> ts){
    return Streams.zip(ts, bs).map((ti,bi) -> normToBound(scope, ti, bi.rcs())).toList();
  }
  private static IT normToBound(List<B> scope, IT t, EnumSet<RC> allowed){
    return xName(t).isEmpty() ? normToBound(t, allowed) : t;
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