package fullWellFormedness;

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
import inferenceGrammar.Impl;
import inferenceGrammar.B;
import inferenceGrammar.Sig;
import inferenceGrammar.Declaration;
import fearlessFullGrammar.TName;

public record InjectionToInferenceVisitor(List<String> implicits, Function<String,String> f, List<Declaration> decs)
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
    var tName= c.name().s();//TODO: apply the rename mapping/add our pkg name
    var tStr= c.name().asUStrLit();
    var arity= c.name().arity();
    var tNameMap= new TName(f.apply(tName),arity,tStr);
    var ts= c.ts().orElse(List.of());
    return new T.C(tNameMap,mapT(ts));
  }
  List<E> mapE(List<fearlessFullGrammar.E> es){ return es.stream().map(e->e.accept(this)).toList(); }
  List<T> mapT(List<fearlessFullGrammar.T> ts){ return ts.stream().map(t->t.accept(this)).toList(); }
  List<IT> mapIT(List<fearlessFullGrammar.T> ts){ return ts.stream().map(t->t.toIT()).toList(); }
  List<T.C> mapC(List<fearlessFullGrammar.T.C> cs){ return cs.stream().map(t->visitC(t)).toList(); }
  List<B> mapB(List<fearlessFullGrammar.B> bs){ return bs.stream().map(b->visitB(b)).toList(); }
  List<T> mapPT(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(p->p.t().get().accept(this)).toList(); }
  List<String> mapPX(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(this::parameterToName).toList(); }
  String parameterToName(fearlessFullGrammar.Parameter p){
    if( p.xp().isEmpty()){ return "_"; }
    XPat xp= p.xp().get();
    return switch(xp){
    case XPat.Name(var x) -> x.name();
    case XPat.Destruct(var _, var _) -> freshPName();
    };
  }  
  List<Sig> mapSig(List<fearlessFullGrammar.M> ms){ return ms.stream().flatMap(this::visitMSig).toList(); }
  List<Impl> mapImpl(List<fearlessFullGrammar.M> ms){ return ms.stream().flatMap(this::visitMImpl).toList(); }
  Stream<Sig> visitMSig(fearlessFullGrammar.M mm){
    if (mm.sig().isEmpty() || mm.hasImplicit()){ return Stream.of(); }
    fearlessFullGrammar.Sig s= mm.sig().get();
    if (!s.fullyTyped()){ return Stream.of(); }
    RC rc= s.rc().orElse(RC.imm);
    MName m= s.m().get();
    List<B> bs= s.bs().map(this::mapB).orElse(List.of());
    List<T> ts= mapPT(s.parameters());
    T res= s.t().get().accept(this);
    return Stream.of(new Sig(rc,m,bs,ts,res,mm.pos()));
  }
  Stream<Impl> visitMImpl(fearlessFullGrammar.M m){
    if (m.body().isEmpty()){ return Stream.of(); }
    var body= m.body().get();
    var original= m.sig().map(s->s.parameters()).orElse(List.of());
    List<String> ps= mapPX(original);
    List<XE> xpats= xpats(ps,original,m.pos());
    if (!xpats.isEmpty()){ throw Bug.todo(); }
    //if xpats, make the Block //TODO: body=...
    if(m.hasImplicit()){ var p= freshPName(); ps = Push.of(ps,p); implicits.add(p); }
    E e= body.accept(this);
    if(m.hasImplicit()){ implicits.removeLast(); }
    Optional<MName> name= m.sig().flatMap(s->s.m());
    return Stream.of(new Impl(name,ps,e));
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
    TName fresh= freshTName();
    T.RCC c= visitRCC(t.t());
    E.Literal l= visitLiteral(t.l().orElseGet(()->empty(t.pos())));
    List<B> bs= freeBs(l);
    List<T> Xs= bs.stream().map(b->(T)b.x()).toList();
    decs.add(new Declaration(fresh,bs,List.of(c.c()),l));
    return new E.Type(new T.RCC(c.rc(),new T.C(fresh, Xs)),u,t.pos());
  }
  private TName freshTName(){ throw Bug.todo(); }//will need the visited chain
  private String freshPName(){ throw Bug.todo(); }//will need the visited chain
  public B visitB(fearlessFullGrammar.B b){ throw Bug.todo(); }
  private List<B> freeBs(E.Literal l){ throw Bug.todo(); }//will need the 
  //storage of Bs in scope
  @Override public E visitDeclarationLiteral(fearlessFullGrammar.E.DeclarationLiteral c){
    TName name= c.dec().name();//TODO: apply the rename mapping/add our pkg name
    E.Literal l= visitLiteral(c.dec().l());
    List<B> bs= c.dec().bs().orElse(List.of()).stream().map(b->visitB(b)).toList();
    List<T> Xs= bs.stream().map(b->(T)b.x()).toList();
    List<T.C> cs= mapC(c.dec().cs());
    RC rc= c.rc().orElse(RC.imm);
    T.C newC= new T.C(name, Xs);
    decs.add(new Declaration(name,bs,cs,l));
    return new E.Type(new T.RCC(rc,newC),u,c.pos());
  }  
  @Override public E.Literal visitLiteral(fearlessFullGrammar.E.Literal l){
    //Optional<E.X> thisName, List<M> methods, Pos pos
    String thisName= l.thisName().map(n->n.name()).orElseGet(()->freshPName());
    List<Sig> sigs= mapSig(l.methods());
    List<Impl> impls= mapImpl(l.methods());
    //TODO: if inferred name -> just extract sigs,impls form l.methods()
    //if given name, should use meths as in the paper ( only need info in the top level decls)
    //can this be relaxed here (just extract) and then enriched outside in visitDeclarationLiteral?
    return new E.Literal(thisName, sigs, impls, u, l.pos());
  }
  @Override public E visitCall(fearlessFullGrammar.E.Call c){
    if (c.pat().isPresent()){ throw Bug.todo(); }
    if (c.targs().isPresent()){ return visitICall(c); }
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