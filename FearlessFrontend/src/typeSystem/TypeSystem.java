package typeSystem;

import static core.RC.*;

import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.function.Function;
import java.util.stream.Collectors;

import core.AllLs;
import core.B;
import core.E;
import core.FearlessException;
import core.LiteralDeclarations;
import core.M;
import core.MName;
import core.OtherPackages;
import core.RC;
import core.Sig;
import core.T;
import core.TName;
import core.TSpan;
import inject.TypeRename;
import message.Err;
import message.Reason;
import message.TypeSystemErrors;
import utils.OneOr;
import utils.Push;
import utils.Range;
import utils.Streams;
import utils.UriSort;
import core.E.*;
import pkgmerge.Package;

public record TypeSystem(TypeScope scope, ViewPointAdaptation v){
  Kinding k(){ return v.k(); }
  public TypeSystemErrors tsE(){ return v.k().tsE(); }
  public Err err(){ return v.k().tsE().err(); }
  public Function<TName,Literal> decs(){ return v.k().tsE().decs(); }
  public record TRequirement(String reqName,T t){}
  public record MType(String promotion,RC rc,List<T> ts,T t){
    MType withPromotion(String promotion){ return new MType(promotion,rc,ts,t); }
  }

  public static void allOk(List<Literal> tops, Package pkg, OtherPackages other){
    tops= UriSort.byFolderThenFile(tops, l->l.span().inner.fileName());
    assert core.AssertNoRepeatedTypeNames.ok(tops);
    Map<TName,Literal> map= AllLs.of(tops);
    Function<TName,Literal> decs= n->LiteralDeclarations._from(n,map::get,other);
    Map<String,String> invMap= pkg.map().entrySet().stream()
      .collect(Collectors.toUnmodifiableMap(Map.Entry::getValue, Map.Entry::getKey));
    var ts= new TypeSystem(TypeScope.top(), new ViewPointAdaptation(new Kinding(new TypeSystemErrors(decs,pkg,invMap))));
    tops.forEach(l->ts.litOk(Gamma.empty(),l));
  }
  public boolean isSub(List<B> bs, T t1, T t2){
    return t1.equals(t2)
      || isXReadImmXSubtype(bs,t1,t2)
      || isSameShapeSubtype(bs,t1,t2)
      || isImplSubtype(bs,t1,t2);
  }
  public void check(List<B> bs, Gamma g, E e, T expected){
    var got= OneOr.of("One reason per requirement", typeOf(bs,g,e,List.of(new TRequirement("", expected))).stream());
    if (got.isEmpty()){ return; }
    throw tsE().methBodyWrongType((TypeScope.Method)scope,e,got,expected);
  }
  List<Reason> typeOf(List<B> bs, Gamma g, E e, List<TRequirement> rs){ return switch (e){
    case X x -> checkX(bs,g,x,rs);
    case Type t -> checkType(bs,g,t,rs);
    case Literal l -> checkLiteral(bs,g,l,rs);
    case Call c -> new CallTyping(this,bs,g,c,rs).run();
  };}
  private List<Reason> checkX(List<B> bs, Gamma g, X x, List<TRequirement> rs){
    var b= g.bind(x.name());
    T declared= b.declared();
    var cur= b.current();
    if (!(cur instanceof Change.WithT w)){ throw tsE().parameterNotAvailableHere(x, (Change.NoT)cur); }
    T got= w.currentT();
    if (rs.isEmpty()){ return List.of(Reason.pass(got)); }
    return rs.stream().map(r->xReason(bs,x,declared,w,r)).toList();
  }
  private Reason xReason(List<B> bs, X x, T declared, Change.WithT w, TRequirement r){
    T got= w.currentT();
    if (isSub(bs,got,r.t())){ return Reason.pass(got); }
    var declaredOk= isSub(bs,declared,r.t());
    return Reason.parameterDoesNotHaveRequiredTypeHere(this,x, r, declared, w, declaredOk);
  }
  private List<Reason> checkType(List<B> bs, Gamma g, Type t, List<TRequirement> rs){
    k().check(t,bs,t.type());
    var ll= decs().apply(t.type().c().name());
    if (!hasInstance(ll)){ throw tsE().typeDeclaredInMethod(t, ll); }
    var rc= t.type().rc();
    var getIso= (rc.isReadOrImm() && !hasAbstractMut(ll)) || rc == mut || rc == mutH;
    var l= ll.withRC(getIso ? iso : rc);
    var tt= getIso ? new Type(t.type().withRC(iso), t.src()) : t;
    l.ms().forEach(m->checkImplemented(l,m,tt));
    return reqs(t,bs,tt.type(),rs);//reqs correctly used for two similar things
  }
  private static boolean hasInstance(Literal l){
    return l.thisName().equals("this") || LiteralDeclarations.has(l.cs(), LiteralDeclarations.captureFree);
  }
  private static boolean hasAbstractMut(Literal l){ return l.ms().stream().anyMatch(m->m.sig().abs() && m.sig().rc() == mut); }
  private List<Reason> reqs(E blame, List<B> bs, T got, List<TRequirement> rs){
    if (rs.isEmpty()){ return List.of(Reason.pass(got)); }
    for (var r : rs){ if (!(r.t() instanceof T.RCC)){ throw tsE().literalImplementsTypeParameter(blame,r.t()); } }
    return rs.stream().map(r->isSub(bs,got,r.t())
      ? Reason.pass(got)
      : Reason.literalDoesNotHaveRequiredType(this,blame,bs,got,r.t())
      ).toList();
  }
  private List<Reason> checkLiteral(List<B> bs1, Gamma g, Literal _l, List<TRequirement> rs){
    var span= _l.name().approxSpan();
    var getIso= ((_l.rc().isReadOrImm() && !hasAbstractMut(_l)) || _l.rc() == mut)
      && _l.thisName().equals("_")
      && new CaptureWalk(bs1,g,RC::isIsoOrImm).isFree(_l);
    _l.onlyImmCapture().inner= new CaptureWalk(bs1,g,rc->rc == imm).isFree(_l);
    var l= getIso ? _l.withRC(iso) : _l;
    for (var r : rs){ if (!(r.t() instanceof T.RCC)){ throw tsE().literalImplementsTypeParameter(l,r.t()); } }
    for (var m : l.ms()){
      var notInferred= m.sig().origin().equals(TypeRename.inferUnknown.c().name());
      if (notInferred){ throw tsE().methodNotInferred(l,m); }
    }
    var ts= dom(l.bs(),span);
    var ms= l.ms().stream().filter(m->m.sig().origin().equals(l.name())).toList();
    var thisType= new T.RCC(l.rc(),new T.C(l.name(),ts),span);
    assert B.xs(bs1).containsAll(B.xs(l.bs()));
    k().check(l,bs1,thisType);
    litOk(g.filterFTV(l),l);
    ms.forEach(m->checkCallable(l,m));
    l.ms().forEach(m->checkImplemented(l,m,l));
    return reqs(l,bs1,thisType,rs);
  }
  private void checkImplemented(Literal l, M m,E blame){
    if (!m.sig().abs()){ return; }
    if (!callable(l.rc(),m.sig().rc())){ return; }
    throw tsE().callableMethodStillAbstract(blame,m);
  }
  private void checkCallable(Literal l, M m){
    if (callable(l.rc(),m.sig().rc())){ return; }
    throw tsE().methodImplementationDeadCode(m, l);
  }
  private boolean callable(RC litRC, RC recRc){ return recRc != mut || !litRC.isReadOrImm(); }

  private record Key(MName m, RC rc){}
  //Sources is needed, not assert only: the user can simply try to override with a non subtype signature.
  //l.ms is the resolved set, either inferred or resolved by hand in a wrong way.
  SequencedMap<Key,List<Sig>> sources(Literal l){
    return Sources.collect(this, l).stream()
      .collect(Collectors.groupingBy(s->new Key(s.m(), s.rc()),LinkedHashMap::new,Collectors.toList()));
  }
  private static final MName asOne= new MName(".as",1);
  private void baseIdOk(Literal l){
    var isBaseId= LiteralDeclarations.has(l.cs(),LiteralDeclarations.baseId);
    if (!isBaseId){ return; }
    var m= OneOr.of("BaseId literals declare only #",l.ms().stream());
    var badBody= m.e().isPresent() && !isId(m);
    if (badBody){ throw tsE().baseIdBadBody(l,m); }
  }
  private boolean isId(M m){
    var x= OneOr.of("BaseId # has one parameter",m.xs().stream());
    return switch (m.e().get()){
      case X e -> e.name().equals(x);
      case Call c -> c.e() instanceof X e && e.name().equals(x) && c.name().equals(asOne)
        && isBaseContainer(m.sig().ts().getFirst());
      default -> false;
    };
  }
  private boolean isBaseContainer(T t){
    return t instanceof T.RCC rcc
      && LiteralDeclarations.has(decs().apply(rcc.c().name()).cs(),LiteralDeclarations.baseContainer);
  }
  private void litOk(Gamma g, Literal l){
    baseIdOk(l);
    var delta= l.bs();
    var span= l.name().approxSpan();
    var selfT= new T.C(l.name(),dom(delta,span));
    sources(l).forEach((k,group)->methodTableOk(l,k,group));
    l.cs().forEach(c->csOk(l,delta,c));
    var g1= v().discard(g,l).add(l.thisName(),new T.RCC(l.rc().isoToMut(),selfT,span));
    l.ms().forEach(m->methOk(l,delta,v().of(g1,l,m),m));//passing l and m instead of their RC for better errors
  }
  private void csOk(Literal l, List<B> delta, T.C c){
    k().checkC(l,delta,c);
    var d= decs().apply(c.name());
    if (!hasInstance(d)){ throw tsE().typeDeclaredInMethod(l, d); }
  }
  private void methOk(Literal forErr,List<B> delta, Gamma g, M m){
    var allBs= Push.of(delta,m.sig().bs());
    m.sig().ts().forEach(t->k().check(forErr,allBs,t));
    k().check(forErr,allBs,m.sig().ret());
    if (m.e().isEmpty()){ return; }
    try{ bodyOk(forErr,allBs,g,m); }
    catch(FearlessException fe){ throw tsE().mCallFrame(m, fe); }
  }
  private void bodyOk(Literal forErr,List<B> delta, Gamma g, M m){
    var ts= m.sig().ts();
    var xs= m.xs();
    g= g.addAll(ts, xs);//Note: 'this' already in g1
    var t= new TypeSystem(scope.pushM(forErr, m),v);
    t.check(delta,g,m.e().get(),m.sig().ret());
    Streams.zip(xs, ts)
      .filter((_,ti)->!k().of(delta,ti,EnumSet.of(mut,read,mutH,readH,imm)))
      .forEach((x,_)->Affine.usedOnce(tsE(),forErr,m,x));
  }
  static List<T> dom(List<B> bs,TSpan span){ return bs.stream().<T>map(b->new T.X(b.x(),span)).toList(); }

  private boolean isImplSubtype(List<B> bs, T t1, T t2){
    if (!(t1 instanceof T.RCC rcc1)){ return false; }
    Literal d= decs().apply(rcc1.c().name());
    return d.cs().stream().anyMatch(ci->isSub(bs, TypeRename.of(new T.RCC(rcc1.rc(), ci,rcc1.span()), B.xs(d.bs()), rcc1.c().ts()), t2));
  }
  private boolean isXReadImmXSubtype(List<B> bs, T t1, T t2){
    return t2 instanceof T.ReadImmX rix
      && t1 instanceof T.X x
      && rix.x().name().equals(x.name())
      && k().of(bs, x, EnumSet.of(iso,imm,mut,read));
  }
  private boolean isSameShapeSubtype(List<B> bs, T t1, T t2){
    if (!eqModXRC(bs,t1.withRC(mut),t2.withRC(mut))){ return false; }
    var rcs2= Kinding.intrinsicRCs(bs, t2);
    return Kinding.intrinsicRCs(bs, t1).stream().allMatch(r1->rcs2.stream().allMatch(r1::isSubType));
  }
  private void methodTableOk(Literal l,Key k,List<Sig> group){
    Sig chosen= Sources.findCanonical(l,k.m(),k.rc());
    assert group.stream().allMatch(s->s.m().equals(chosen.m()) && s.rc() == chosen.rc());
    assert mostSpecificByOrigin(group,chosen);
    assert absPreserved(chosen);//This assert and the one below do the same thing in working programs but may differ in buggy ones
    assert group.stream().filter(s->s.origin().equals(chosen.origin())).allMatch(s->chosen.abs() == s.abs());
    for (var s:group){ sigSub(l,chosen,s); }
    assert concreteConflictsSolved(group,chosen);
  }
  private boolean concreteConflictsSolved(List<Sig> group,Sig chosen){
    return group.stream().filter(s->!s.abs())
      .allMatch(s->isOriginSub(chosen.origin(),s.origin()));
  }
  private boolean mostSpecificByOrigin(List<Sig> group, Sig chosen){
    for (var s : group){
      if (s.equals(chosen)){ continue; }
      assert !s.origin().equals(chosen.origin()):
        s+" "+chosen+"""
        The assert above is actually a big deal. It can logically break in an better version of Fearless
        when inference would know about subtypes when selecting the 'chosen'.
        Same origin can appear multiple times when the same generic supertype is inherited with
        different instantiation arguments (Fearless allows this; Java forbids it).
        Currently, Fearless requires the programmer to select a winning signature by overriding it.
        """;
      assert !isOriginSub(s.origin(),chosen.origin());
    }
    return true;
  }
  private boolean absPreserved(Sig chosen){
    Literal o= decs().apply(chosen.origin());
    Sig src= Sources.findCanonical(o,chosen.m(),chosen.rc());
    assert !src.abs() || chosen.abs();
    return true;
  }
  private boolean isOriginSub(TName sub, TName sup){
    return sub.equals(sup) || decs().apply(sub).cs().stream().anyMatch(parent->isOriginSub(parent.name(), sup));
  }
  private void sigSub(Literal l, Sig current, Sig parent){
    assert current.bs().equals(parent.bs());
    List<B> ctx= Push.of(l.bs(),current.bs());
    assert current.ts().size() == parent.ts().size();
    for (int i : Range.of(current.ts())){
      var badArg= !isSub(ctx, parent.ts().get(i), current.ts().get(i));
      if (badArg){ throw tsE().methodOverrideSignatureMismatchContravariance(this,ctx,l,current,parent, i); }
    }
    var badRet= !isSub(ctx, current.ret(), parent.ret());
    if (badRet){ throw tsE().methodOverrideSignatureMismatchCovariance(this,ctx,l,current,parent); }
  }
  private boolean eqModXRC(List<B> bs,T a,T b){
    if (a.equals(b)){ return true; }
    var redundantRcOnB= a instanceof T.X ax && b instanceof T.RCX br && br.x().name().equals(ax.name()) && redundantOnX(bs,br.rc(),ax.name());
    if (redundantRcOnB){ return true; }
    var redundantRcOnA= a instanceof T.RCX ar && b instanceof T.X bx && ar.x().name().equals(bx.name()) && redundantOnX(bs,ar.rc(),bx.name());
    if (redundantRcOnA){ return true; }
    if (!(a instanceof T.RCC aa && b instanceof T.RCC bb)){ return false; }
    var sameHead= aa.rc() == bb.rc() && aa.c().name().equals(bb.c().name());
    if (!sameHead){ return false; }
    return Streams.zip(aa.c().ts(), bb.c().ts()).allMatch((x,y)->eqModXRC(bs,x,y));
  }
  private boolean redundantOnX(List<B> bs,RC rc,String x){ return get(bs,x).rcs().equals(EnumSet.of(rc)); }
}