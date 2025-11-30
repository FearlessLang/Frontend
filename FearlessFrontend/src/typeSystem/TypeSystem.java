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
    T got= check(bs,g,e,intrinsicRCs(bs,expected));
    if(isSub(bs,got,expected)){ return; }
    throw TypeSystemErrors.typeError(e.pos(),got, expected);
  }
  private T check(List<B> bs, Gamma g, E e, EnumSet<RC> expected){ return switch (e){
    case X x -> checkX(bs,g,x); 
    case Type t -> checkType(bs,g,t);
    case Literal l -> checkLiteral(bs,g,l);
    case Call c -> checkCall(bs,g,c,expected);
  };}  
  private T checkX(List<B> bs, Gamma g, X x){ return g.get(x.name()); }//TODO: consider just inlining this method?  
  private T checkType(List<B> bs, Gamma g, Type t){ return t.type(); }//TODO: consider just inlining this method?
  private T checkLiteral(List<B> bs1, Gamma g, Literal l) {
    var ts= l.bs().stream().<T>map(b->new T.X(b.x())).toList();
    var ms= l.ms().stream().filter(m->m.sig().origin().equals(l.name())).toList();
    ms.forEach(m->checkCallable(l.rc(), m));
    l.ms().forEach(m->checkImplemented(l.rc(),m));
    T thisType= new T.RCC(l.rc(),new T.C(l.name(),ts));
    assert l.bs().stream().allMatch(b->bs1.stream().anyMatch(b1->b.x().equals(b1.x())));
    k().of(bs1, thisType);
    litOk(g.filterFTV(l.bs()),l);
    return thisType;
  }
  private T checkCall(List<B> bs, Gamma g, Call c, EnumSet<RC> expected) {
    throw Bug.todo();
  }  
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
    l.cs().stream().map(c->new T.RCC(RC.mut,c)).forEach(c->k().of(delta,c));
    var g1= g.add(l.thisName(),new T.RCC(l.rc().isoToMut(),selfT));
    l.ms().forEach(m->{
      Gamma g2= v().of(g1,delta,l.rc(),m.sig().rc());
      methOk(delta,g2,m);
    });
  }
  private void methOk(List<B> delta, Gamma g, M m){
    var allBs= Push.of(delta,m.sig().bs());
    m.sig().ts().forEach(t->k().of(allBs,t));
    k().of(allBs,m.sig().ret());
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
  private EnumSet<RC> intrinsicRCs(List<B> bs, T t){ return switch(t){
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