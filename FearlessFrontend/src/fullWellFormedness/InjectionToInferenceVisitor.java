package fullWellFormedness;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import utils.Bug;
import utils.Push;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.Parameter;
import fearlessFullGrammar.XPat;
import fearlessParser.RC;
import files.Pos;
import inferenceGrammar.T;
import inferenceGrammar.E;
import inferenceGrammar.IT;
import inferenceGrammar.M;
import inferenceGrammar.B;
import inferenceGrammar.Declaration;
import fearlessFullGrammar.TName;

public record InjectionToInferenceVisitor(List<TName> tops, List<String> implicits, Function<TName,TName> f, List<Declaration> decs, Package pkg, List<List<B>> bsInScope, OtherPackages other, FreshPrefix freshF)
    implements fearlessFullGrammar.EVisitor<inferenceGrammar.E>,fearlessFullGrammar.TVisitor<T>{
  static final inferenceGrammar.IT u= IT.U.Instance;
  static fearlessFullGrammar.E.Literal empty(Pos pos){ return new fearlessFullGrammar.E.Literal(Optional.empty(),List.of(),pos); }
  @Override public T.X visitTX(fearlessFullGrammar.T.X x){ return new T.X(x.name()); }
  @Override public T visitReadImmX(fearlessFullGrammar.T.ReadImmX x){ return new T.ReadImmX(visitTX(x.x())); }
  @Override public T visitRCX(fearlessFullGrammar.T.RCX x){ return new T.RCX(x.rc(), visitTX(x.x())); }
  @Override public T.RCC visitRCC(fearlessFullGrammar.T.RCC c){
    return new T.RCC(c.rc().orElse(RC.imm),visitC(c.c()));
  }
  public T.C visitC(fearlessFullGrammar.T.C c){
    var tName= c.name();
    var tNameMap= f.apply(tName);
    var ts= c.ts().orElse(List.of());
    return new T.C(tNameMap,mapT(ts));
  }
  List<E> mapE(List<fearlessFullGrammar.E> es){ return es.stream().map(e->e.accept(this)).toList(); }
  List<T> mapT(List<fearlessFullGrammar.T> ts){ return ts.stream().map(t->t.accept(this)).toList(); }
  List<IT> mapIT(List<fearlessFullGrammar.T> ts){ return ts.stream().map(t->t.toIT()).toList(); }
  List<T.C> mapC(List<fearlessFullGrammar.T.C> cs){ return cs.stream().map(t->visitC(t)).toList(); }
  List<B> mapB(List<fearlessFullGrammar.B> bs){ return bs.stream().map(b->visitB(b)).toList(); }
  List<Optional<T>> mapPT(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(p->p.t().map(ti->ti.accept(this))).toList(); }
  List<String> mapPX(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(this::parameterToName).toList(); }
  String parameterToName(fearlessFullGrammar.Parameter p){
    if( p.xp().isEmpty()){ return "_"; }
    XPat xp= p.xp().get();
    return switch(xp){
    case XPat.Name(var x) -> x.name();
    case XPat.Destruct(var _, var _) -> freshF.freshVar(tops.getLast(), "div");
    };
  }  
  List<M> mapM(List<fearlessFullGrammar.M> ms){ return ms.stream().map(this::visitM).toList(); }
  M visitM(fearlessFullGrammar.M m){ return new M(visitMSig(m),visitMImpl(m)); }
  M.Sig visitMSig(fearlessFullGrammar.M mm){
    if(mm.sig().isEmpty()){
      List<Optional<T>> ts= !mm.hasImplicit()?List.of():List.of(Optional.empty());
      return new M.Sig(Optional.empty(),Optional.empty(),Optional.empty(),ts,Optional.empty(),mm.pos()); 
    }
    fearlessFullGrammar.Sig s= mm.sig().get();
    Optional<List<B>> bs= s.bs().map(this::mapB);
    List<Optional<T>> ts= mapPT(s.parameters());
    if (mm.hasImplicit()){ ts= Push.of(ts,Optional.empty()); }
    Optional<T> res= s.t().map(ti->ti.accept(this));
    return new M.Sig(s.rc(),s.m(),bs,ts,res,mm.pos());
  }
  public B visitB(fearlessFullGrammar.B b){
    return new B(visitTX(b.x()),switch(b.bt()){
    case fearlessFullGrammar.B.Star()->List.of(RC.imm,RC.mut,RC.read);
    case fearlessFullGrammar.B.StarStar()->List.of(RC.imm, RC.mut, RC.read, RC.iso, RC.mutH, RC.readH);
    case fearlessFullGrammar.B.RCS(List<RC> rcs)-> rcs.isEmpty()
      ?List.of(RC.imm)
      :inDeclarationOrder(rcs,b.x());
    });
  }
  private static List<RC> inDeclarationOrder(List<RC> es, fearlessFullGrammar.T.X x){
    if (es.size() != new HashSet<>(es).size()){
      throw WellFormednessErrors.duplicatedBound(es,x);
    }
    return es.stream().sorted(Comparator.comparingInt(Enum::ordinal)).toList();
  }

  Optional<M.Impl> visitMImpl(fearlessFullGrammar.M m){
    if (m.body().isEmpty()){ return Optional.empty(); }
    m.sig().ifPresent(s->bsInScope.add(s.bs().map(this::mapB).orElse(List.of())));
    var body= m.body().get();
    var original= m.sig().map(s->s.parameters()).orElse(List.of());
    List<String> ps= mapPX(original);
    List<XE> xpats= xpats(ps,original,m.pos());
    if (!xpats.isEmpty()){ throw Bug.todo(); }
    //if xpats, make the Block //TODO: body=...
    if (m.hasImplicit()){ var p= freshF.freshVar(tops.getLast(), "impl"); ps = Push.of(ps,p); implicits.add(p); }
    E e= body.accept(this);
    m.sig().ifPresent(_->bsInScope.removeLast());
    if (m.hasImplicit()){ implicits.removeLast(); }
    Optional<MName> name= m.sig().flatMap(s->s.m());
    return Optional.of(new M.Impl(name,ps,e));
  }
  record XE(String x, E e){}
  boolean isXPat(fearlessFullGrammar.Parameter p){
    return p.xp().isPresent() && p.xp().get() instanceof XPat.Destruct; 
  }
  List<XE> xpats(List<String> lowered, List<fearlessFullGrammar.Parameter> original, Pos pos){
    assert lowered.size() == original.size();
    return IntStream.range(0,lowered.size()).boxed()
      .filter(i->isXPat(original.get(i)))
      .flatMap(i->xpat((XPat.Destruct)original.get(i).xp().get(),lowered.get(i),pos))
      .toList();
  }
  Stream<XE> xpat(XPat.Destruct pat, String fresh, Pos pos){
    List<String> patterns = pat.parameterNames().toList();
    assert pat.extract().size() == patterns.size();
    return IntStream.range(0,patterns.size())
      .mapToObj(i->xpat(pat.extract().get(i),patterns.get(i),fresh,pos));
  }
  XE xpat(List<MName> pat, String x, String fresh, Pos pos){
    E res= new E.X(fresh, u, pos);
    for (MName m:pat){ res= new E.ICall(res,m,List.of(), u, pos); }
    return new XE(fresh,res);
  }
  @Override public E visitX(fearlessFullGrammar.E.X x){ return new E.X(x.name(),u,x.pos()); }
  @Override public E visitRound(fearlessFullGrammar.E.Round r){ return r.e().accept(this); }
  @Override public E visitImplicit(fearlessFullGrammar.E.Implicit n){  return new E.X(implicits.getLast(),u,n.pos());  }
  @Override public E visitTypedLiteral(fearlessFullGrammar.E.TypedLiteral t){
    var summon= t.l().map(l->l.methods().isEmpty()).orElse(true);
    T.RCC c= visitRCC(t.t());
    if (summon){ return new E.Type(c,u,t.pos()); }
    E.Literal l= visitLiteral(t.l().orElseGet(()->empty(t.pos())));
    List<B> bs= freeBs(c,l);
    List<T> Xs= bs.stream().map(b->(T)b.x()).toList();
    TName fresh= freshF.freshTopType(c.c().name(),Xs.size());
    decs.add(new Declaration(fresh,bs,List.of(c.c()),l));
    return new E.Type(new T.RCC(c.rc(),new T.C(fresh, Xs)),u,t.pos());
  }
  private List<B> freeBs(T.RCC c, E.Literal l){
    return Stream.concat(new FreeXs().ftvE(l),new FreeXs().ftvT(c))
      .map(x->xB(x)).toList();
  }
  B xB(T.X x){ return bsInScope.stream().flatMap(List::stream).filter(b->b.x().equals(x)).findFirst().get(); }
  @Override public E visitDeclarationLiteral(fearlessFullGrammar.E.DeclarationLiteral c){
    var dec= addDeclaration(c.dec(),false);
    List<T> Xs= dec.bs().stream().map(b->(T)b.x()).toList();
    RC rc= c.rc().orElse(RC.imm);
    T.C newC= new T.C(dec.name(), Xs);
    return new E.Type(new T.RCC(rc,newC),u,c.pos());
  }
  public Declaration addDeclaration(fearlessFullGrammar.Declaration d, boolean top){
    TName name= f.apply(d.name());
    tops.add(name);
    List<B> bs= d.bs().map(this::mapB).orElse(List.of());
    bsInScope.add(bs);    
    E.Literal l= visitLiteral(d.l(),top);
    List<T.C> cs= mapC(d.cs());
    var res= new Declaration(name,bs,cs,l);
    decs.add(res);
    bsInScope.removeLast();
    return res;
  }
  @Override public E.Literal visitLiteral(fearlessFullGrammar.E.Literal l){
    return visitLiteral(l,false);
  }
  public E.Literal visitLiteral(fearlessFullGrammar.E.Literal l, boolean top){
    String thisName= l.thisName().map(n->n.name()).orElseGet(()->top?"this":"_");
    List<M> ms= mapM(l.methods());
    //TODO: if inferred name -> just extract sigs,impls form l.methods()
    //if given name, should use meths as in the paper ( only need info in the top level decls)
    //can this be relaxed here (just extract) and then enriched outside in visitDeclarationLiteral?
    return new E.Literal(thisName, ms, u, l.pos());
  }
  @Override public E visitCall(fearlessFullGrammar.E.Call c){
    if (c.pat().isPresent()){ throw Bug.todo(); }
    if (c.targs().isEmpty()){ return visitICall(c); }
    E e= c.e().accept(this);
    var targs= c.targs().get();
    List<E> es= mapE(c.es());
    List<IT> ts= mapIT(targs.ts());
    return new E.Call(e, c.name(), targs.rc(), ts, es, u, c.pos());
  }
  public E visitICall(fearlessFullGrammar.E.Call c){
    E e= c.e().accept(this);
    List<E> es= mapE(c.es());
    return new E.ICall(e, c.name(), es, u, c.pos());
  }
  @Override public E visitStringInter(fearlessFullGrammar.E.StringInter i){ throw Bug.todo(); }
  
  @Override public XPat visitInnerXPat(fearlessFullGrammar.XPat x){ throw Bug.unreachable(); }
  @Override public fearlessFullGrammar.M visitInnerM(fearlessFullGrammar.M m){ throw Bug.unreachable(); }
  @Override public fearlessFullGrammar.Sig visitInnerSig(fearlessFullGrammar.Sig s){ throw Bug.unreachable(); }
  @Override public Parameter visitInnerParameter(fearlessFullGrammar.Parameter p){ throw Bug.unreachable(); }
  @Override public fearlessFullGrammar.B visitInnerB(fearlessFullGrammar.B b){ throw Bug.unreachable(); }
  @Override public fearlessFullGrammar.E.Literal visitInnerLiteral(fearlessFullGrammar.E.Literal l){ throw Bug.unreachable(); }
  @Override public fearlessFullGrammar.Declaration visitInnerDeclaration(fearlessFullGrammar.Declaration d){ throw Bug.unreachable(); }
  
  @Override public fearlessFullGrammar.T.RCC visitInnerRCC(fearlessFullGrammar.T.RCC t){ throw Bug.unreachable(); }
  @Override public fearlessFullGrammar.E.CallSquare visitInnerCallSquare(fearlessFullGrammar.E.CallSquare c){ throw Bug.unreachable(); }

}