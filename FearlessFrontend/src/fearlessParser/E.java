package fearlessParser;

import java.util.*;
import java.util.function.Function;

import files.Pos;
import utils.Bug;
import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

record TName(String s, int arity){
  public TName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert validate(s,"TName", UppercaseId,UnsignedInt, SignedInt, SignedRational, Float, UStr, SStr);
  }
  public TName withArity(int arity){ return new TName(s,arity); }
}
record MName(String s, int arity){
  public MName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert validate(s,"MName", DotName, Op);
  }
  public MName withArity(int arity){ return new MName(s,arity); }
}
sealed interface T {
  <R> R accept(TVisitor<R> v);
  record X(String name) implements T{
    public X{assert validate(name,"generic type name", _XId);}
    public <R> R accept(TVisitor<R> v){ return v.visitX(this); }
  }
  record RCX(RC rc, X x) implements T{
    public RCX{assert nonNull(rc,x);}
    public <R> R accept(TVisitor<R> v){ return v.visitRCX(this); }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{assert nonNull(x);}
    public <R> R accept(TVisitor<R> v){ return v.visitReadImmX(this); }
  }
  record C(TName name, Optional<List<T>> ts){
    public C{
      assert validOpt(ts,_ts->{
        unmodifiable(_ts,"T.C.args");
        eq(_ts.size(), name.arity(),"Type arity");
      });
    }
    public  C accept(TVisitor<?> v){ return v.visitInnerC(this); }
  }
  record RCC(Optional<RC> rc, C c) implements T{
    public RCC{ nonNull(rc,c); }
    public <R> R accept(TVisitor<R> v){ return v.visitRCC(this); }
  }
}
sealed interface E {
  Pos pos();
  <R> R accept(EVisitor<R> v);
  record X(String name, Pos pos) implements E{
    public X{ assert validate(name, "parameter name",LowercaseId); }
    public <R> R accept(EVisitor<R> v){ return v.visitX(this); }
    public String toString(){ return name; }
  }
  record Round(E e) implements E{
    public Round{ assert nonNull(e); }
    public Pos pos(){ return e.pos(); }
    public <R> R accept(EVisitor<R> v){ return v.visitRound(this); }
    public String toString(){ return "("+e+")"; }
  }
  record Literal(Optional<E.X> thisName, List<M> methods,Pos pos) implements E{
    public Literal{
      assert unmodifiable(methods, "L.Full.methods");
      assert nonNull(thisName);
    }
    public <R> R accept(EVisitor<R> v){ return v.visitLiteral(this); }
    public String toString(){ return "Literal"+thisName.map(Object::toString).orElse("")+methods; }
  }
  record TypedLiteral(T.RCC t,Optional<Literal> l,Pos pos) implements E{
    public TypedLiteral{ assert nonNull(t,l); }
    public <R> R accept(EVisitor<R> v){ return v.visitTypedLiteral(this); }
    public String toString(){ return "TypedLiteral"+t+l.map(Object::toString).orElse(""); }
  }
  record DeclarationLiteral(Optional<RC> rc, Declaration dec) implements E{
    public DeclarationLiteral{ assert nonNull(rc,dec); }
    public <R> R accept(EVisitor<R> v){ return v.visitDeclarationLiteral(this); }
    public Pos pos(){ return dec.pos(); }
    public String toString(){ return "DeclarationLiteral"+rc.map(Object::toString).orElse("")+dec; }
  }
  //if pat is present, this is an x=e posts, if absent this is a normal meth call.
  record CallSquare(Optional<RC> rc, List<T> ts){
    public CallSquare{ assert nonNull(rc) && unmodifiable(ts, "E.Call.targs"); }
  }
  record Call(E e, MName name, Optional<CallSquare> targs, boolean pars, Optional<XPat> pat, List<E> es, Pos pos) implements E{
    public Call{
      assert nonNull(e,name,targs,pat);
      assert unmodifiable(es, "E.Call.es");
      assert pat.isPresent() || eq(es.size(),name.arity(),"Call arity");
      assert pars || es.size() < 2;
      assert validOpt(pat,_->eq(es.size(),1,"invalid equal sugar"));
      assert validOpt(pat,_->eq(name.arity(),2,"invalid equal sugar"));
    }
    public <R> R accept(EVisitor<R> v){ return v.visitCall(this); }
    public String toString(){ return "Call["+e+"]"+name
      +targs.map(Object::toString).orElse("")
      +pars+pat.map(Object::toString).orElse("")+es; }
  }
  record StringInter(boolean simple, Optional<E> receiver, List<Integer> hashCounts, List<String> strings, List<E> es,Pos pos) implements E{
    public StringInter{
      assert nonNull(receiver);
      assert unmodifiable(strings,"string parts");
      assert unmodifiable(es,"string es");
      assert eq(strings.size(),es.size()+1,"string interpolation");
    }
    public <R> R accept(EVisitor<R> v){ return v.visitStringInter(this); }
    public String toString(){ return "Inter["+simple+"]"
      +receiver.map(Object::toString).orElse("")
      +hashCounts+strings.stream().map(s->s.replace("\n","\\n")).toList()+es;
    }
  }
  record Implicit(Pos pos) implements E{ 
    public <R> R accept(EVisitor<R> v){ return v.visitImplicit(this); }
    public String toString(){ return "::"; }
  }
}
record Declaration(TName name, Optional<List<B>> bs, List<T.C> cs, E.Literal l){
  Declaration{
    assert nonNull(name,l);
    assert bs.isPresent() || name.arity() == 0:" name arity should be zero";
    assert validOpt(bs,b->{
      unmodifiable(b, "E.TypeDeclarationLiteral.bs");
      eq(name.arity(),b.size(),"E.TypeDeclarationLiteral.bs");
    });    
  }
  public Pos pos(){ return l.pos(); }
}
sealed interface XPat {
  <R> R accept(XPatVisitor<R> v);
  record Name(E.X x) implements XPat{
    public Name{ assert nonNull(x); }
    public <R> R accept(XPatVisitor<R> v){ return v.visitXPatName(this);}
  }
  //xE ::= x m* is represented as an element of extract, for example 
  //new Destruct(List.of(List.of(.foo,.bar,.baz),List.of(.x.y)),Optional.of("1"))
  //represents {foo.bar.baz,x.y}1 
  record Destruct(List<List<MName>> extract, Optional<String> id) implements XPat{
    public Destruct{
      assert unmodifiable(extract, "ParamPat.Destruct.extract",
        sm->unmodifiable(sm,"ParamPat.Destruct.extract element",
          m->{assert m.s().startsWith(".");}));
      assert validOpt(id,n -> validate("}"+n, "pattern id",CCurlyId));
    }
    public <R> R accept(XPatVisitor<R> v){ return v.visitXPatDestruct(this);}
  }
}
record M(Optional<Sig> sig, Optional<E> body){
  public M{
    assert nonNull(sig,body);
    assert sig.isPresent() || body.isPresent();
  }
}
interface BT{}
record Star() implements BT{}
record StarStar() implements BT{}
record RCS(List<RC> rcs) implements BT{
  RCS{//if rcs is empty, it means absence of :RCs
    assert unmodifiable(rcs,"B.rcs");
    assert rcs.isEmpty() || rcs.equals(List.copyOf(EnumSet.copyOf(rcs)));//check the order is normalized  
  }}
record B(T.X x, BT bt){ B{ assert nonNull(x,bt);}}

record Parameter(Optional<XPat> xp, Optional<T> t){
  Parameter{ assert xp.isPresent() || t.isPresent(); }
  XPat toXPat(){
    if(xp.isEmpty()){ throw Bug.of(); }
    if(t.isPresent()){ throw Bug.of(); }
    return xp.get();
  }
  T toT(){
    if(xp.isPresent()){ throw Bug.of(); }
    if(t.isEmpty()){ throw Bug.of(); }
    return t.get();
  }
}
record Sig(
  Optional<RC> rc, Optional<MName> m,
  Optional<List<B>> bs, boolean hasParenthesis,
  List<Parameter> parameters, Optional<T> t
  ){
  Sig{
    assert nonNull(rc,m,bs,parameters,t);
    assert validOpt(m,_m->eq(_m.arity(),parameters.size(),"Method name arity"));
  }
}
record Use(TName global, T.X local){
  public Use{
    assert nonNull(global,local);
    assert global.s().contains("."); 
  }
}

record FileFull(List<Use> renames, List<Declaration> decs){
  public FileFull{
    assert unmodifiable(renames, "FileFull.renames");
    assert unmodifiable(decs, "FileFull.decs");
  }
}
interface EVisitor<R>{
  R visitX(E.X n);
  R visitRound(E.Round r);
  R visitImplicit(E.Implicit n);
  R visitTypedLiteral(E.TypedLiteral t);
  T.RCC visitInnerRCC(T.RCC t);
  R visitDeclarationLiteral(E.DeclarationLiteral c);
  R visitLiteral(E.Literal c);
  R visitCall(E.Call c);
  E.CallSquare visitInnerCallSquare(E.CallSquare c);
  R visitStringInter(E.StringInter i);
  XPat visitInnerXPat(XPat x);
  M visitInnerM(M m);
  Sig visitInnerSig(Sig s);
  Parameter visitInnerParameter(Parameter p);
  B visitInnerB(B b);
  E.Literal visitInnerLiteral(E.Literal l);
  Declaration visitInnerDeclaration(Declaration d);
  default MName visitInnerMName(MName n){ return n; }
  default E.X visitInnerX(E.X n){ return n; }
  default <RR> List<RR> mapEs(List<E> es, Function<E,RR> f){ return es.stream().map(f).toList(); }
  default <RR> List<RR> mapBs(List<B> bs, Function<B,RR> f){ return bs.stream().map(f).toList(); }
  default <RR> List<RR> mapPs(List<Parameter> ps, Function<Parameter,RR> f){ return ps.stream().map(f).toList(); }
}
interface TVisitor<R>{
  R visitX(T.X x);
  R visitRCX(T.RCX x);
  R visitReadImmX(T.ReadImmX x);
  R visitRCC(T.RCC c);
  default TName visitInnerTName(TName n){ return n; }
  default T.X   visitInnerX(T.X x){ return x; }
  default T.C   visitInnerC(T.C c){ return c; }
  default RC    visitInnerRC(RC rc){ return rc; }
  default <RR> List<RR> mapTs(List<T> ts, Function<T,RR> f){ return ts.stream().map(f).toList(); }
}
interface XPatVisitor<R>{
  R visitXPatName(XPat.Name n);
  R visitXPatDestruct(XPat.Destruct d);
}
interface Visitor<RE,RT,RXPat> extends EVisitor<RE>,TVisitor<RT>,XPatVisitor<RXPat>{}
/*
interface CloneVisitor extends Visitor<E,T,XPat> {
  @Override default E visitX(E.X n){ return visitInnerX(n);}
  @Override default E visitImplicit(E.Implicit n){ return n; }
  @Override default E visitTypedLiteral(E.TypedLiteral t){
    return new E.TypedLiteral(
      visitInnerRCC(t.t()),
      visitInnerLiteral(t.l()));
  }
  @Override default E visitDeclarationLiteral(E.DeclarationLiteral d){
    return new E.DeclarationLiteral(
      d.rc().map(this::visitInnerRC),
      visitInnerDeclaration(d.dec()));
  }
  @Override default E visitLiteral(E.Literal l){ return visitInnerLiteral(l); }
  @Override default E.Literal visitInnerLiteral(E.Literal l){
    return new E.Literal(l.pos(),
      l.thisName().map(this::visitInnerX),
      l.methods().stream().map(this::visitInnerM).toList());
  }
  @Override default E visitCall(E.Call n){
    var    _e= n.e().accept(this);
    var _name= visitInnerMName(n.name());
    var   _ts= n.targs().map(this::visitInnerCallSquare);
    var  _pat= n.pat().map(this::visitInnerXPat);
    var   _es= mapEs(n.es(), ei -> ei.accept(this));
    return new E.Call(n.pos(),_e, _name, _ts, _pat, _es);
  }
  @Override default E.CallSquare visitInnerCallSquare(E.CallSquare c){
    var  _rc= c.rc().map(this::visitInnerRC);
    var  _ts= mapTs(c.ts(), t -> t.accept(this));
    return new E.CallSquare(_rc, _ts);
  }
  @Override default E visitStringInter(E.StringInter n){
    var recv= n.receiver().map(e -> e.accept(this));
    var strs= n.strings();
    var es= mapEs(n.es(), e -> e.accept(this));
    return new E.StringInter(n.pos(),n.simple(), recv, strs, es);
  }
  @Override default M visitInnerM(M m){
    var  sig= visitInnerSig(m.sig());
    var body= m.body().map(e -> e.accept(this));
    return new M(sig, body);
  }
  default Sig visitInnerSig(Sig s){
    var _rc= s.rc().map(this::visitInnerRC);
    var  _m= s.m().map(this::visitInnerMName);
    var _bs= s.bs().map(bs->mapBs(bs,this::visitInnerB));
    var _ps= mapPs(s.parameters(),this::visitInnerParameter);
    var  _t= s.t().map(t->t.accept(this));
    return new Sig(_rc,_m,_bs,s.hasParenthesis(),_ps,s.hasImplicit(),_t);
  }
  @Override default XPat visitInnerXPat(XPat x){ return x.accept(this); }
  @Override default XPat visitXPatName(XPat.Name n){ return new XPat.Name(visitInnerX(n.x())); }
  @Override default XPat visitXPatDestruct(XPat.Destruct d){
    var extract= d.extract().stream()
      .map(path -> path.stream().map(this::visitInnerExtract).toList())
      .toList();
    var id= d.id().map(this::visitInnerId);
    return new XPat.Destruct(extract, id);
  }
  @Override default T visitX(T.X x){ return visitInnerX(x); }
  @Override default T visitRCX(T.RCX x){ return new T.RCX(visitInnerRC(x.rc()),visitInnerX(x.x())); }
  @Override default T visitReadImmX(T.ReadImmX x){ return new T.ReadImmX(visitInnerX(x.x())); }
  @Override default T.C visitInnerC(T.C c){ return new T.C(visitInnerTName(c.name()),mapTs(c.ts(), t->t.accept(this))); }
  @Override default T visitRCC(T.RCC c){ return visitInnerRCC(c); }
  @Override default T.RCC visitInnerRCC(T.RCC c){ return new T.RCC(c.rc().map(this::visitInnerRC), visitInnerC(c.c())); }
}*/

/*
interface CollectorVisitor extends Visitor<Void,Void,Void,Void> {
  @Override default Void visitX(E.X n){ visitInnerX(n); return null; }
  @Override default Void visitImplicit(E.Implicit n){ return null; }
  @Override default Void visitTypedLiteral(E.TypedLiteral t){
    t.t().accept(this);
    visitInnerLiteral(t.l());
    return null; 
    }
  @Override default Void visitLiteral(E.Literal l){ visitInnerLiteral(l); return null; }
  @Override default E.Literal visitInnerLiteral(E.Literal l){
    l.thisName().ifPresent(this::visitInnerX);
    l.methods().forEach(m->visitInnerM(m));
    return null;
  }
  @Override default Void visitCall(E.Call n){
    n.e().accept(this);
    visitInnerMName(n.name());
    n.targs().ifPresent(ts -> ts.forEach(t -> t.accept(this)));
    n.pat().ifPresent(this::visitInnerXPat);
    n.es().forEach(a -> a.accept(this));
    return null;
  }
  @Override default Void visitStringInter(E.StringInter i){
    i.receiver().ifPresent(r -> r.accept(this));
    i.es().forEach(e -> e.accept(this));
    return null;
  }
  @Override default M visitInnerM(M m){
    m.sig().accept(this);
    m.body().ifPresent(e -> e.accept(this));
    return m;
  }
  @Override default XPat visitInnerXPat(XPat x){
    x.accept(this);
    return x;
  }
  @Override default B visitInnerB(B b){
    b.x().accept(this);
    b.rcs().forEach(this::visitInnerRC);
    return b;
  }
  @Override default Void visitXPatName(XPat.Name n){
    n.x().accept(this);
    return null;
  }
  @Override default Void visitXPatDestruct(XPat.Destruct d){
    d.extract().forEach(path -> path.forEach(this::visitInnerMName));
    d.id().ifPresent(this::visitInnerId);
    return null;
  }
  @Override default String visitInnerId(String id){ return id; }
  @Override default MName visitInnerExtract(MName n){ return visitInnerMName(n); }

  @Override default Void visitExplicit(Sig.Explicit s){
    visitInnerRC(s.rc());
    visitInnerMName(s.name());
    s.bs().forEach(this::visitInnerB);
    s.pars().forEach(this::visitInnerPar);
    s.ret().accept(this);
    return null;
  }
  @Override default Void visitInferred(Sig.Inferred s){
    s.name().ifPresent(this::visitInnerMName);
    s.ps().forEach(this::visitInnerXPat);
    return null;
  }
  @Override default Void visitColonColon(Sig.ColonColon s){
    s.name().ifPresent(this::visitInnerMName);
    return null;
  }
  @Override default Sig.Par visitInnerPar(Sig.Par p){
    visitInnerXPat(p.xPat());
    p.t().accept(this);
    return p;
  }
  @Override default Void visitX(T.X x){
    visitInnerX(x);
    return null;
  }
  @Override default Void visitRCX(T.RCX x){
    visitInnerRC(x.rc());
    visitInnerX(x.x());
    return null;
  }
  @Override default Void visitReadImmX(T.ReadImmX x){
    visitInnerX(x.x());
    return null;
  }
  @Override default T.C visitInnerC(T.C c){
    visitInnerTName(c.name());
    c.ts().forEach(t -> t.accept(this));
    return c;
  }
  @Override default Void visitRCC(T.RCC c){
    visitInnerRC(c.rc());
    visitInnerC(c.c());
    return null;
  }
  @Override default TName visitInnerTName(TName n){ return n; }
  @Override default T.X   visitInnerX(T.X x){ return x; }
  @Override default RC    visitInnerRC(RC rc){ return rc; }
  @Override default MName visitInnerMName(MName n){ return n; }
}
*/