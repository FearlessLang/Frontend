package typeSystem;

import java.util.EnumSet;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import core.B;
import core.E;
import core.M;
import core.Sig;
import core.T;
import fearlessParser.RC;
import inject.TypeRename;
import message.TypeSystemErrors;
import pkgmerge.OtherPackages;
import typeSystem.ArgMatrix.*;

import static fearlessParser.RC.*;
import utils.Bug;
import utils.OneOr;
import utils.Push;
import core.E.*;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;

public record TypeSystem(ViewPointAdaptation v){
  Kinding k(){ return v.k(); }
  Function<TName,Literal> decs(){ return v.k().decs(); }
  public record TRequirement(String reqName,T t){}
  public record MType(String promotion,RC rc,List<T> ts,T t){}
  List<MType> multiMeth(List<B> bs1, MType mType){ throw Bug.todo(); }

  public static void allOk(List<Literal> tops, OtherPackages other){
    var map= AllLs.of(tops);
    Function<TName,Literal> decs= n->map.getOrDefault(n,other.of(n)); //TODO: not very efficient
    var ts= new TypeSystem(new ViewPointAdaptation(new Kinding(decs)));
    tops.forEach(l->ts.litOk(Gamma.empty(),l));
  }
  public boolean isSub(List<B> bs, T t1, T t2){
    return t1.equals(t2)
      || isXReadImmXSubtype(bs,t1,t2)
      || isSameShapeSubtype(bs,t1,t2)
      || isImplSubtype(bs,t1,t2);
  }
  public void check(List<B> bs, Gamma g, E e, T expected){
    var rs= List.of(new TRequirement("", expected));
    var out= typeOf(bs,g,e,rs);
    assert out.size() == 1;
    if (out.getFirst().success()){ return; }
    throw TypeSystemErrors.typeError(e.pos(),out,rs);
  }
  List<TResult> typeOf(List<B> bs, Gamma g, E e, List<TRequirement> rs){ return switch(e){
    case X x -> checkX(bs,g,x,rs);
    case Type t -> checkType(bs,g,t,rs);
    case Literal l -> checkLiteral(bs,g,l,rs);
    case Call c -> checkCall(bs,g,c,rs);
  };}
  private List<TResult> checkX(List<B> bs, Gamma g, X x, List<TRequirement> rs){
    return reqs(bs,g.get(x.name()),rs);
  }
  private List<TResult> checkType(List<B> bs, Gamma g, Type t, List<TRequirement> rs){
    return reqs(bs,t.type(),rs);
  }
  private List<TResult> checkLiteral(List<B> bs1, Gamma g, Literal l, List<TRequirement> rs){
    var ts= l.bs().stream().<T>map(b->new T.X(b.x())).toList();
    var ms= l.ms().stream().filter(m->m.sig().origin().equals(l.name())).toList();
    ms.forEach(m->checkCallable(l.rc(),m));
    l.ms().forEach(m->checkImplemented(l.rc(),m));
    T thisType= new T.RCC(l.rc(),new T.C(l.name(),ts));
    assert l.bs().stream().allMatch(b->bs1.stream().anyMatch(b1->b.x().equals(b1.x())));
    k().check(bs1,thisType);
    litOk(g.filterFTV(l.bs()),l);
    return reqs(bs1,thisType,rs);
  }
  private List<TResult> reqs(List<B> bs, T got, List<TRequirement> rs){
    if (rs.isEmpty()){ return List.of(new TResult("",got,"")); }
    return rs.stream().map(r->{
      if (isSub(bs,got,r.t())){ return new TResult(r.reqName(),got,""); }
      return new TResult(r.reqName(),got,"got "+got+" not subtype of "+r.t());
    }).toList();//TODO: ideally, can we get a readable representation of the e? the name for x, the meth name for call, the type for Type and the Type (or implemented single interface if type is anon) for lambda
  }
  private List<TResult> checkCall(List<B> bs,Gamma g,Call c, List<TRequirement> rs){
    return new CallTyping(this,bs,g,c,rs).run();
  }

/*
∆′, Γ ⊢ e0 : RC0 D[T0] //
m[∆]:Ts′ → T′ = meth(D[T0], m) // 
∆′ ⊢ Ts : ∆//notation defined  below //
m[]:T0 T1 . . . T𝑛 → T ∈ multiMeth(∆′, (m[∆]:T′ → T′)[∆ = Ts])//declare multi meth abstract, we define it later
∆′ ⊢ RC0 D[T0] ≤ T0
∆′, Γ ⊢ e1 : T1 . . . ∆′, Γ ⊢ e𝑛 : T𝑛
--------------------------------------------------------------
∆′, Γ ⊢ e0 m[Ts](e1, . . . e𝑛) : T

∆′ ⊢ T : ∆
∆ ⊢ (T1 . . . T𝑛) : (X1 : RCs1 . . . X𝑛 : RCs𝑛) holds iff ∆ ⊢ T1 : RCs1 . . . ∆ ⊢ T𝑛 : RCsn
*/
 
  /*private T __checkCall(List<B> bs1, Gamma g, Call c, EnumSet<RC> expected){
    T recvT= check(bs1,g,c.e(),EnumSet.of(c.rc()));
    if(!(recvT instanceof T.RCC rcc0)){ throw TypeSystemErrors.methodNotFoundOnReceiver(c); }
    T.C c0= rcc0.c();
    Literal d= decs().apply(c0.name());
    Sig sig= OneOr.of("Missing or Duplicate meth",
    d.ms().stream().map(M::sig).filter(s->s.m().equals(c.name()) && s.rc()==c.rc()));
    assert sig.ts().size()==c.es().size();//Well formedness already
    if(sig.bs().size()!=c.targs().size()){ throw TypeSystemErrors.methodTArgsArityError(c); }
    assert c0.ts().size() == d.bs().size();
    var targs= c.targs();
    for(int i= 0; i < targs.size(); i++){
      k().check(bs1,targs.get(i),EnumSet.copyOf(sig.bs().get(i).rcs()));
    }
    var allXs= Stream.concat(d.bs().stream(),sig.bs().stream()).map(B::x).toList();
    var allTs= Push.of(c0.ts(),c.targs());
    var ps= TypeRename.ofT(sig.ts(),allXs,allTs);
    T ret= TypeRename.of(sig.ret(),allXs,allTs);
    List<MType> mTypes= multiMeth(bs1,new MType(sig.rc(),ps,ret));
    return mTypes.stream()
      .????(m->checkMType(bs1,g,m,rcc0.rc(),c.es()))
      .????;//we need to select so that the mType return type intrinsicRCs
      //is compatible with the expected rcs.
      //Logically, we could just try them all and for all the one that pass
      //check if any of them would produce intrinsicRCs that would satisfy
      //the incoming subtype test     if(isSub(bs,got,expected)){ return; }
      //but probably we can make a better job, like selecting the ones
      //with hope of success first.
      //also we should prioritize the ones with a 'better' return.
      //this is easy when intrinsicRCs is a singleton (just the one with the most specific type)
      //but could be harder when the intrinsicRCs is some arbitrary set 
  }
  private ??? checkMType(List<B> bs, Gamma g, MType m,RC rc,List<E> es){
    if (!rc.isSubType(m.rc())){ nope }
    for(int i= 0; i < es.size(); i++){
      check(bs,g,es.get(i),m.ts().get(i));//either pass or nope
      }
    //if no nopes, this pass
    }*/
  //multiMeth will return a set of possible methods. The idea is that they are only going
  //to be different over the RC + read/imm components while keeping the nominal aspect constant.
  //multiMeth is the way fearless allows to promote mut to iso and read to imm when possible.
  
  
  private void checkImplemented(RC litRC, M m){
    if (!callable(litRC,m.sig().rc())){ return; }
    throw TypeSystemErrors.callableMethodAbstract(m.sig().pos(), m, litRC);
  }
  private void checkCallable(RC litRC, M m){
    if (callable(litRC,m.sig().rc())){ return; }
    throw TypeSystemErrors.uncallableMethodDeadCode(m.sig().pos(), m, litRC);
  }
  private boolean callable(RC litRC, RC recRc){ return recRc != RC.mut || (litRC != RC.imm && litRC !=RC.read); }

  private record Key(MName m, RC rc){}
  Map<Key,List<Sig>> sources(Literal l){ 
    return Sources.collect(this, l).stream()
      .collect(Collectors.groupingBy(s -> new Key(s.m(), s.rc())));
  }
  private void litOk(Gamma g, Literal l){
    var delta= l.bs();
    var selfT= new T.C(l.name(),dom(delta));
    var sources= sources(l);
    assert l.ms().stream().map(M::sig).allMatch(s->sources.containsKey(new Key(s.m(),s.rc())));
    //overrideOk(l,sources);  implementOk(l,sources);
    sources.forEach((k,group)->methodTableOk(l,k,group));
    l.cs().stream().map(c->new T.RCC(RC.mut,c)).forEach(c->k().check(delta,c));
    var g1= g.add(l.thisName(),new T.RCC(l.rc().isoToMut(),selfT));
    l.ms().forEach(m->{
      Gamma g2= v().of(g1,delta,l.rc(),m.sig().rc());
      methOk(delta,g2,m);
    });
  }
  private void methOk(List<B> delta, Gamma g, M m){
    var allBs= Push.of(delta,m.sig().bs());
    m.sig().ts().forEach(t->k().check(allBs,t));
    k().check(allBs,m.sig().ret());
    if(!m.e().isEmpty()){ bodyOk(allBs,g,m); }
  }
  private void bodyOk(List<B> delta, Gamma g, M m){
    var ts= m.sig().ts();
    var xs= m.xs();
    g= g.addAll(ts, xs);//Note: 'this' already in g1
    check(delta,g,m.e().get(),m.sig().ret());
    for(int i= 0; i < xs.size(); i++){
      var isAffine= !k().of(delta,ts.get(i),EnumSet.of(mut,read,mutH,readH,imm));
      if (isAffine){ Affine.usedOnce(xs.get(i),m.e().get()); }
    }
  }  
  private List<T> dom(List<B> bs){ return bs.stream().<T>map(b->new T.X(b.x())).toList(); }
  
  private boolean isImplSubtype(List<B> bs, T t1, T t2){
    if (!(t1 instanceof T.RCC rcc1)){ return false; }
    Literal d= decs().apply(rcc1.c().name());
    List<String> xs= d.bs().stream().map(B::x).toList();
    for (T.C ci : d.cs()){
      T sup= TypeRename.of(new T.RCC(rcc1.rc(), ci), xs, rcc1.c().ts());
      if (isSub(bs, sup, t2)){ return true; }
    }
    return false;
  }
  private boolean isXReadImmXSubtype(List<B> bs, T t1, T t2){
    return t2 instanceof T.ReadImmX rix
      && t1 instanceof T.X x
      && rix.x().name().equals(x.name())
      && k().of(bs, x, EnumSet.of(iso,imm,mut,read));
  }
  private boolean isSameShapeSubtype(List<B> bs, T t1, T t2){
    if (!t1.withRC(mut).equals(t2.withRC(mut))){ return false; }
    var rcs1= intrinsicRCs(bs, t1);
    var rcs2= intrinsicRCs(bs, t2);
    for (var r1 : rcs1){
      for (var r2 : rcs2){
        if (!r1.isSubType(r2)){ return false; }
      }
    }
    return true;
  }
  EnumSet<RC> intrinsicRCs(List<B> bs, T t){ return switch(t){
    case T.RCC(var rc, _) -> EnumSet.of(rc);
    case T.RCX(var rc, _) -> EnumSet.of(rc);
    case T.X(var x) -> EnumSet.copyOf(get(bs, x).rcs());
    case T.ReadImmX x -> intrinsicRCs(bs,x);
  };}
  private EnumSet<RC> intrinsicRCs(List<B> bs, T.ReadImmX x){
    var rcs= get(bs, x.x().name()).rcs();
    if (EnumSet.of(iso, imm).containsAll(rcs)){ return EnumSet.of(imm); }
    if (EnumSet.of(mut, mutH, read, readH).containsAll(rcs)){ return EnumSet.of(read); }
    return EnumSet.of(read, imm);
  }
  private B get(List<B> bs, String name){
    return OneOr.of("Type variable not found",bs.stream().filter(b->b.x().equals(name)));
  }
  private static Sig findCanonical(Literal l, MName name, RC rc){
    return OneOr.of("Missing or Duplicate meth",l.ms().stream().map(M::sig).filter(s->s.m().equals(name) && s.rc() == rc));
  }
  private void methodTableOk(Literal l,Key k,List<Sig> group){
    Sig chosen= findCanonical(l,k.m(),k.rc());
    assert group.contains(chosen);
    assert mostSpecificByOrigin(group,chosen);
    assert absPreserved(chosen);//This assert and the one below do the same thing in working programs but may differ in buggy ones
    assert group.stream().filter(s->s.origin().equals(chosen.origin())).allMatch(s->chosen.abs() == s.abs());
    for(var s:group){ sigSub(l.bs(),chosen,s); }
    assert concreteConflictsSolved(group,chosen);
  }
  private boolean concreteConflictsSolved(List<Sig> group,Sig chosen){
    return group.stream().filter(s->!s.abs())
      .allMatch(s->isOriginSub(chosen.origin(),s.origin()));
  }
  private boolean mostSpecificByOrigin(List<Sig> group, Sig chosen){
    for (var s : group){
      if (s.equals(chosen)){ continue; }
      assert !s.origin().equals(chosen.origin()):"""
        The assert above is actually a big deal. It can logically break in an better version of Fearless
        when inference would know about subtypes when selecting the 'chosen'.
        Same origin can appear multiple times when the same generic supertype is inherited with
        different instantiation arguments (Fearless allows this; Java forbids it).
        Currently, Fearless requires the programmer to select a winning signature by overriding it.
        """;
      assert !isOriginSub(s.origin(),chosen.origin()) : "Resolver not most specific: chosen "+chosen.origin().s()+" but "+s.origin().s()+" exists";
    }
    return true;
  }
  private boolean absPreserved(Sig chosen){
    Literal o= decs().apply(chosen.origin());
    Sig src= findCanonical(o,chosen.m(),chosen.rc());
    assert !src.abs() || chosen.abs():"Abstractness mismatch";
    return true;
  }  
  private boolean isOriginSub(TName sub, TName sup){
    if (sub.equals(sup)){ return true; }
    Literal d= decs().apply(sub);
    for (var parent : d.cs()){ if (isOriginSub(parent.name(), sup)){ return true; } }
    return false;
  }

  private void sigSub(List<B> ctx, Sig sub, Sig sup){
    var bsSub= sub.bs();
    var bsSup= sup.bs();
    assert bsSub.size() == bsSup.size();//TODO: if we can trigger this, then we have problems in Sources.canonical
    for (int i= 0; i < bsSub.size(); i++){
      var badBounds= !bsSub.get(i).rcs().equals(bsSup.get(i).rcs());
      if (badBounds){ throw TypeSystemErrors.overrideMismatch(sub, sup, "Generic bounds mismatch for " + bsSub.get(i).x()); }
    }
    assert bsSub.equals(bsSup);
    ctx= Push.of(ctx,bsSub);
    var badArity= sup.ts().size() != sub.ts().size();
    if (badArity){ throw TypeSystemErrors.overrideMismatch(sub,sup, "Arity mismatch"); }
    for (int i= 0; i < sub.ts().size(); i++){
      var badArg= !isSub(ctx, sup.ts().get(i), sub.ts().get(i));
      if (badArg){ throw TypeSystemErrors.overrideMismatch(sub,sup, "Argument " + i + " type mismatch (contravariance violation)"); }
    }
    var badRet= !isSub(ctx, sub.ret(), sup.ret());
    if (badRet){ throw TypeSystemErrors.overrideMismatch(sub, sup, "Return type mismatch (covariance violation)"); }
  }
}