package inject;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.Sig;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import inference.E;
import inference.Gamma;
import inference.IT;
import inference.M;
import toInfer.FreeXs;
import utils.Bug;
import utils.OneOr;
import utils.Push;

public record InjectionSteps(Methods meths){
  public static List<core.E.Literal> steps(Methods meths, List<inference.E.Literal> tops){
    var s= new InjectionSteps(meths);
    List<core.E.Literal> res= new ArrayList<>();
    for (var l : tops){
      assert l.thisName().equals("this");
      res.add(s.stepDec(meths.cache().get(l.name()), l));
    }
    return List.copyOf(res);
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
    List<IT> thisTypeTs= di.bs().stream().<IT>map(b -> new IT.X(b.x())).toList();
    List<String> xs= m.impl().get().xs();
    var thisType= new IT.RCC(mCore.sig().rc(), new IT.C(di.name(), thisTypeTs));//no preferred on self names
    inference.E ei= meet(e, TypeRename.tToIT(mCore.sig().ret()));
    Gamma g= Gamma.of(xs, TypeRename.tToIT(mCore.sig().ts()), di.thisName(), thisType);
    ei = nextStar(Push.of(di.bs(), m.sig().bs().get()), g, ei);
    return new core.M(mCore.sig(), xs, Optional.of(new ToCore().of(ei, m.impl().get().e())));
  }
  static E meet(E e, IT t){
    var tt= meet(e.t(), t);
    if (tt instanceof IT.Err){ return e; }
    return e.withT(tt);
  }
  static IT meet(IT t1, IT t2){
    if (t2 == IT.U.Instance){ return t1; }
    if (t1 == IT.U.Instance){ return t2; }
    if (t1.equals(t2)){ return t1; }
    if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){
      if (!x1.c().name().equals(x2.c().name())){ return IT.Err.Instance; }
      assert x1.c().ts().size() == x2.c().ts().size();
      RC rc= meetRcNoH(x1.rc(), x2.rc());
      var ts= meet(x1.c().ts(), x2.c().ts());
      return x1.withRCTs(rc,ts);
    }
    if (t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX x2){
      if (!x1.x().equals(x2.x())){ return IT.Err.Instance; }
      RC rc= meetRcNoH(x1.rc(), x2.rc());
      return x1.withRC(rc);
    }
    return IT.Err.Instance;
  }
  static RC meetRcNoH(RC a, RC b){
    if (a == b){ return a; }
    if (a == RC.iso){ return noH(b); }
    if (b == RC.iso){ return noH(a); }
    return RC.read;
  }
  static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
  static List<IT> meet(List<IT> t1, List<IT> t2){
    assert t1.size() == t2.size() : "should have gone in Err before";
    return IntStream.range(0, t1.size()).mapToObj(i -> meet(t1.get(i), t2.get(i))).toList();
  }
  static List<IT> meet(List<List<IT>> tss){
    var first= tss.getFirst();
    int size= first.size();
    assert tss.stream().allMatch(ts -> ts.size() == size);
    var res= new ArrayList<IT>(size);
    for (int i= 0; i < size; i++){
      var curr= first.get(i);
      for (int j= 1; j < tss.size(); j++){ curr = meet(curr, tss.get(j).get(i)); }
      res.add(curr);
    }
    return Collections.unmodifiableList(res);
  }
  E nextStar(List<B> bs, Gamma g, E e){
    if (e.done(g)){ return e; }
    while (true){
      var s= g.snapshot();
      var oe= next(bs, g, e);
      //assert oe == e || g.changed(s) || !oe.equals(e) : "Allocated equal E:"+e.getClass()+"\n"+e;
      if (oe == e && !g.changed(s)){ e.sign(g); return e; }
      //if (oe.equals(e) && !g.changed(s)){ e.sign(g); return e; }//this line is useful for debugging when == gets buggy
      e = oe;
    }
  }
  private List<E> meet(List<E> es, MSigL m, List<IT> targs){
    boolean same= true;
    var res= new ArrayList<E>(es.size());
    for (int i= 0; i < es.size(); i += 1){
      E next= meet(es.get(i), m.p(i,targs));
      same &= next == es.get(i);
      res.add(next);
    }
    if (same){ return es; }
    return Collections.unmodifiableList(res);
  }
  private List<E> nextStar(List<B> bs, Gamma g, List<E> es){
    var s= g.snapshot();
    boolean same= true;
    var res= new ArrayList<E>(es.size());
    for (E ei : es){
      E next= nextStar(bs, g, ei);
      same &= next == ei;
      res.add(next);
    }
    if (same && !g.changed(s)){ return es; }
    return Collections.unmodifiableList(res);
  }
  E next(List<B> bs, Gamma g, E e){ return switch (e){
    case E.X x -> nextX(bs, g, x);
    case E.Literal l -> nextL(bs, g, l);
    case E.Call c -> nextC(bs, g, c);
    case E.ICall c -> nextIC(bs, g, c);
    case E.Type c -> nextT(bs, g, c);
  };}
  core.E.Literal getDec(TName name){ return meths.from(name); }
  private IT preferred(IT.RCC type){
    var d= getDec(type.c().name());
    assert d != null : type;
    var cs= d.cs().stream().filter(c -> c.name().s().equals("base.WidenTo")).toList();
    if (cs.isEmpty()){ return type; }
    assert cs.size() == 1;
    assert cs.getFirst().ts().size() == 1;
    var dom= d.bs().stream().map(b -> b.x()).toList();
    IT wid= TypeRename.of(TypeRename.tToIT(cs.getFirst().ts().getFirst()), dom, type.c().ts());
    var w=(IT.RCC)wid;//TODO: this must be made to fail in a test, then we need to improve the well formedness error of WidenTo
    return new IT.RCC(type.rc(), w.c());
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
    var d= getDec(rcc.c().name());
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
    var t3= meet(t1, t2);
    if (t3 instanceof IT.Err){ return x; }
    g.update(x.name(), t3);
    return x.withT(t3);
  }
  private E nextT(List<B> bs, Gamma g, E.Type t){
    var t1= preferred(t.type());
    var t2= t.t();
    if (t1.equals(t2)){ return t; }
    var t3= meet(t1, t2);
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
    var t= meet(c.t(), m.ret(ts));
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
    List<IT> targs= newTargs(c, es, m);
    var it= meet(c.t(), m.ret(targs));
    var es1= meet(es, m, targs);
    if (e == c.e() && es == c.es() && targs.equals(c.targs()) && it.equals(c.t())){ return c; }
    return c.withMore(e, rc, targs, es1, it);
  }
  private List<IT> newTargs(E.Call c, List<E> es, MSigL m){
    int n= m.bsArity();
    if (n == 0){ return List.of(); }
    if (c.targs().size()!= n){ return c.targs(); } //Note: this will eventually become an error at type system time.
    assert c.targs().isEmpty() || c.targs().size() == n;
    List<String> methXs= m.methXs();
    var a= IntStream.range(0, c.es().size())
      //.mapToObj(i->refine(methXs, m.pStr(i,m.methXs()), es.get(i).t()));//THIS FAILS tests
      .mapToObj(i->refine(methXs, m.ps0().get(i), es.get(i).t()));
    var r= Stream.of(refine(methXs, m.ret0(), c.t()), c.targs());
    List<List<IT>> tss= Stream.concat(a,r).toList();
    return meet(tss);
  }  
  private Optional<IT.RCC> preciseSelf(E.Literal l){
    if (l.rc().isEmpty()){ return Optional.empty(); }
    var xs= l.bs().stream().<IT>map(b -> new IT.X(b.x())).toList();
    return Optional.of(new IT.RCC(l.rc().get(), new IT.C(l.name(), xs)));
  }
  private Optional<IT.RCC> superSelf(E.Literal l){
    if (l.cs().size() != 1){ return preciseSelf(l); }
    if (l.rc().isEmpty()){ return Optional.empty(); }
    return Optional.of(new IT.RCC(l.rc().get(), l.cs().getFirst()));
  }

  private E nextL(List<B> bs, Gamma g, E.Literal l){
    var infA= l.infA();//TODO: is there some case where infA != l.rc().isPresent()? assert it?
    if (!l.infA() && !l.cs().isEmpty()){ l = meths.expandDeclaration(l); }
    var selfPrecise= preciseSelf(l);
    var selfSuper= superSelf(l);
    if (l.rc().isPresent() && l.t() instanceof IT.U){ l = l.withT(preferred(selfSuper.get())); }
    if (!(l.t() instanceof IT.RCC rcc)){ return l; }
    if (!l.infA()){ assert l.cs().isEmpty(); l = meths.expandLiteral(l, rcc.c()); }
    boolean changed= false;
    var res= new ArrayList<inference.M>(l.ms().size());
    List<IT> ts= rcc.c().ts();
    var selfT= selfPrecise.filter(_ -> infA);// TODO: is this already implicitly the case? Check!
    for (var mi : l.ms()){
      if (mi.impl().isEmpty()){ res.add(mi); continue; } // we are also keeping methods from supertypes, and not all will be in need of implementation
      TSM next= nextMStar(bs, g, l.thisName(), meths.cache().containsKey(l.name()), selfT, rcc, ts, mi);
      changed |= next.m != mi || !next.ts.equals(ts);
      res.add(next.m);
      ts = next.ts;
    }
    if (!changed){ return commitToTable(bs, l, rcc); }
    var ms= Collections.unmodifiableList(res);
    IT t= rcc.withTs(ts);
    return commitToTable(bs, l.withMsT(ms, t), t);
  }
  private E commitToTable(List<B> bs, E.Literal l, IT t){
    if (l.rc().isPresent() || !t.isTV() || !(t instanceof IT.RCC rcc) || hasU(l.ms())){ return l; }
    assert l.cs().isEmpty();
    assert l.bs().isEmpty() : "bs must stay empty pre-commit";
    var noMeth= l.ms().stream().allMatch(m -> m.impl().isEmpty());
    if (noMeth){ return new E.Type(rcc, rcc, l.src(), l.g()); } // TODO: what if it was not a fresh name but a user defined name?
    List<IT.C> cs= Push.of(rcc.c(), meths.fetchCs(rcc.c()));
    meths.checkMagicSupertypes(l.name(), cs);
    var freeNames= Stream.concat(new FreeXs().ftvMs(l.ms()), new FreeXs().ftvCs(l.cs()));
    List<B> localBs= freeNames.distinct().map(x -> RC.get(bs, x)).toList();
    TName name= l.name();
    TName newName= name.withArity(localBs.size());
    List<M> ms= l.ms().stream().map(m -> fixArity(m, name, newName)).toList();
    l = new E.Literal(Optional.of(rcc.rc()), newName, localBs, cs, l.thisName(), ms, t, l.src(), true, l.g());
    var resD= meths.injectDeclaration(l);
    meths.cache().put(resD.name(), resD);// can we simply remove dsMap and use meth cache all the time?
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
  private static List<Optional<IT>> updateArgs(List<String> xs, List<Optional<IT>> old, Gamma g) {
    int n= xs.size();
    assert old.size() == n;
    boolean changed= false;
    ArrayList<Optional<IT>> out= new ArrayList<>(n);
    for (int i= 0; i < n; i++){
      var x= xs.get(i);
      var oi= old.get(i);
      if ("_".equals(x)){ out.add(oi); continue; }
      assert oi.isPresent();
      var ti= g.get(x);
      if (oi.get().equals(ti)){ out.add(oi); continue; }
      changed = true;
      out.add(Optional.of(ti));
    }
    return changed ? Collections.unmodifiableList(out) : old;
  }
  record TSM(List<IT> ts, inference.M m){}
  private TSM nextMStar(List<B> bs, Gamma g, String thisN, boolean committed, Optional<IT.RCC> selfPrecise, IT.RCC rcc, List<IT> ts, inference.M m){
    assert selfPrecise.isEmpty() || rcc.isTV();
    assert m.impl().isPresent();
    var sig0= m.sig();
    var impl0= m.impl().get();
    rcc = rcc.withTs(ts);
    RC mrc= sig0.rc().get();
    RC thisRc= (mrc == RC.read && rcc.rc() == RC.imm) ? RC.imm : mrc;
    IT selfT= selfPrecise.<IT>map(it -> it.withRC(thisRc)).orElse(IT.U.Instance);    
    MName mName= sig0.m().get();
    var size= mName.arity();
    var xs= impl0.xs();
    var args= sig0.ts();
    g.newScope();
    g.declare(thisN, selfT);
    for (int i= 0; i < size; i += 1){ g.declare(xs.get(i), args.get(i).get()); }
    var bsBodyEnv= Push.of(bs, sig0.bs().get());
    E e= nextStar(bsBodyEnv, g, impl0.e());
    args = updateArgs(xs, args, g);
    g.popScope();
    if (committed){
      if (e == impl0.e()){ return new TSM(ts, m); }
      return new TSM(ts, new inference.M(sig0, Optional.of(impl0.withE(e))));
    }
    var improvedSig= sig0.withTsT(args, e.t());
    var ret= improvedSig.ret().get();
    ts = rcc.c().ts();
    var sigTs= improvedSig.ts();
    // Note: imh has the Xs in place, both type and meth. No rename needed
    var omh= methodHeaderAnd(rcc, mName, improvedSig.rc(), (_, _, mi) -> mi);// Now the assert in methodHeaderInstance is failing, so this is suspiscius
    assert omh.isEmpty() || assertNoBinderClash(rcc, omh.get());
    if (omh.isEmpty()){
      var impl= impl0.withE(meet(e, ret));
      if (improvedSig == sig0 && impl == impl0){ return new TSM(ts, m); }
      return new TSM(ts, new inference.M(improvedSig, Optional.of(impl)));
    }
    var Xs= getDec(rcc.c().name()).bs().stream().map(b -> b.x()).toList();
    Sig imh= omh.get().sig();
    ts = meet(Stream.concat(
      IntStream.range(0, imh.ts().size())
        .mapToObj(i -> refine(Xs, TypeRename.tToIT(imh.ts().get(i)), sigTs.get(i).get())),
      Stream.of(refine(Xs, TypeRename.tToIT(imh.ret()), ret), ts)).toList());
    rcc = rcc.withTs(ts);
    var targetBs= improvedSig.bs().isEmpty()
      ? List.<String>of()
      : improvedSig.bs().get().stream().map(b->b.x()).toList();
    MSigL h= methodHeader(rcc, mName, improvedSig.rc()).get();
    assert h.bsArity() == targetBs.size();
    M.Sig sigRes= improvedSig.withTsT(
      h.psStr(targetBs),
      h.retStr(targetBs));
    //TODO: this comment comes from an older version. Is still relevant?"""Overall we should apply normalizeHeaderBs only if selfPrecise is absent;
    //otherwise assert that the Xs are the righ ones"""
    e = meet(e, sigRes.ret().get());
    var impl= impl0.withE(e);
    if (sigRes == sig0 && impl == impl0){ return new TSM(rcc.c().ts(), m); }
    return new TSM(rcc.c().ts(), new inference.M(sigRes, Optional.of(impl)));
  }
  private boolean assertNoBinderClash(IT.RCC rcc, core.M m){
    var cls= getDec(rcc.c().name()).bs().stream().map(b -> b.x()).toList();
    var meth= m.sig().bs().stream().map(b -> b.x()).toList();
    return Collections.disjoint(cls, meth);
  }  
  List<IT> refine(List<String> xs, IT t, IT t1){
    if (t1 instanceof IT.U){ return qMarks(xs.size()); }
    return switch (t){
      case IT.X x -> refineXs(xs, x, t1);
      case IT.RCX(RC _, IT.X x) -> refineXs(xs, x, t1);
      case IT.ReadImmX(IT.X x) -> refineXs(xs, x, t1);
      case IT.RCC(RC _, IT.C c) -> propagateXs(xs, c, t1);
      case IT.U _ -> qMarks(xs.size());
      case IT.Err _ -> qMarks(xs.size());
    };
  }
  List<IT> refineXs(List<String> xs, IT.X x, IT t1){
    var i= xs.indexOf(x.name());
    if (i == -1){ return qMarks(xs.size()); }
    return qMarks(i, t1, xs.size());
  }
  List<IT> propagateXs(List<String> xs, IT.C c, IT t1){
    if (t1 instanceof IT.U || t1 instanceof IT.Err){ return qMarks(xs.size()); }
    if (!(t1 instanceof IT.RCC cc)){ throw Bug.unreachable(); }//not assert to declare cc
    if (!cc.c().name().equals(c.name())){ return qMarks(xs.size()); }
    assert cc.c().ts().size() == c.ts().size();
    List<List<IT>> res= IntStream.range(0, c.ts().size())
      .mapToObj(i -> refine(xs, c.ts().get(i), cc.c().ts().get(i))).toList();
    return res.isEmpty() ? qMarks(xs.size()) : meet(res);
  }
}
//record MSig(RC rc, List<String> bs, List<IT> ts, IT ret) {}
record MSigL(RC rc, List<String> xs, List<IT> clsArgs, List<IT> ps0, IT ret0){
  int arity(){ return ps0.size(); }
  int nCls(){ return clsArgs.size(); }
  int bsArity(){ return xs.size() - nCls(); }
  List<String> methXs(){ return xs.subList(nCls(), xs.size()); }
  IT p(int i, List<IT> targs){ return inst(ps0.get(i), targs); }
  IT ret(List<IT> targs){ return inst(ret0, targs); }
  private IT inst(IT t, List<IT> targs){
    if (targs.size() != bsArity()){ return t; }//Note: this will eventually become an error at type system time.
    var ts= Push.of(clsArgs,targs);
    return TypeRename.of(t, xs, ts);
  }
  IT pStr(int i, List<String> targetBs){ return inst(ps0.get(i), toXs(targetBs)); }
  List<Optional<IT>> psStr(List<String> targetBs){
    assert targetBs.size() == bsArity();
    var ts= toXs(targetBs);
    return ps0.stream().map(p->Optional.of(inst(p, ts))).toList();
  }
  IT retStr(List<String> targetBs){
    assert targetBs.size() == bsArity();
    return inst(ret0, toXs(targetBs));    
  }
  private List<IT> toXs(List<String> targetBs){ return targetBs.stream().<IT>map(IT.X::new).toList(); }
}