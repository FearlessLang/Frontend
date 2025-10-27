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
import fearlessFullGrammar.E.Call;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.Parameter;
import fearlessFullGrammar.XPat;
import fearlessParser.RC;
import files.Pos;
import inferenceGrammar.T;
import message.WellFormednessErrors;
import inferenceGrammar.E;
import inferenceGrammar.IT;
import inferenceGrammar.M;
import inferenceGrammar.B;
import inferenceGrammar.Declaration;
import fearlessFullGrammar.TName;
import static java.util.Optional.*;

public record InjectionToInferenceVisitor(List<TName> tops, List<String> implicits, Function<TName,TName> f, List<Declaration> decs, Package pkg, List<List<B>> bsInScope, OtherPackages other, FreshPrefix freshF)
    implements fearlessFullGrammar.EVisitor<inferenceGrammar.E>,fearlessFullGrammar.TVisitor<T>{
  static final inferenceGrammar.IT u= IT.U.Instance;
  static fearlessFullGrammar.E.Literal emptyL(Pos pos){ return new fearlessFullGrammar.E.Literal(empty(),List.of(),pos); }
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
      List<Optional<T>> ts= !mm.hasImplicit()?List.of():List.of(empty());
      return new M.Sig(Optional.empty(),empty(),empty(),ts,empty(),mm.pos()); 
    }
    fearlessFullGrammar.Sig s= mm.sig().get();
    Optional<List<B>> bs= s.bs().map(this::mapB);
    List<Optional<T>> ts= mapPT(s.parameters());
    if (mm.hasImplicit()){ ts= Push.of(ts,empty()); }
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
    if (m.body().isEmpty()){ return empty(); }
    m.sig().ifPresent(s->bsInScope.add(s.bs().map(this::mapB).orElse(List.of())));
    var body= m.body().get();
    var original= m.sig().map(s->s.parameters()).orElse(List.of());
    List<String> ps= mapPX(original);
    List<XE> xpats= xpats(ps,original,m.pos());
    if (!xpats.isEmpty()){ body = makeXPatsBody(body,xpats); }
    if (m.hasImplicit()){ var p= freshF.freshVar(tops.getLast(), "impl"); ps = Push.of(ps,p); implicits.add(p); }
    E e= body.accept(this);
    m.sig().ifPresent(_->bsInScope.removeLast());
    if (m.hasImplicit()){ implicits.removeLast(); }
    Optional<MName> name= m.sig().flatMap(s->s.m());
    return of(new M.Impl(name,ps,e));
  }
  private fearlessFullGrammar.E makeXPatsBody(fearlessFullGrammar.E body, List<XE> xes){
    var p= body.pos();
    //Block#.let x1={e1}.. .let xn={en}.return{body}
    var block0= new fearlessFullGrammar.T.RCC(
      of(RC.imm),
      new fearlessFullGrammar.T.C(new TName("base.Block",0,p),of(List.of())));
    fearlessFullGrammar.E blockE= new fearlessFullGrammar.E.TypedLiteral(block0, empty(),p);
    blockE = new fearlessFullGrammar.E.Call(blockE, new MName("#",0),empty(),false,empty(),List.of(),p);
    for(var xe:xes){
      var xp= new fearlessFullGrammar.XPat.Name(new fearlessFullGrammar.E.X(xe.x,p));
      var e= new fearlessFullGrammar.E.Literal(empty(),List.of(new fearlessFullGrammar.M(empty(),of(xe.e), false,p) ),p);
      blockE = new fearlessFullGrammar.E.Call(blockE, new MName(".let",2),empty(),false,of(xp),List.of(e),p); 
    }
    var b= new fearlessFullGrammar.E.Literal(empty(),List.of(new fearlessFullGrammar.M(empty(),of(body), false,p) ),p);
    return new fearlessFullGrammar.E.Call(blockE, new MName(".return",1),empty(),false,empty(),List.of(b),p);
  }
  record XE(String x, fearlessFullGrammar.E e){}
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
    fearlessFullGrammar.E res= new fearlessFullGrammar.E.X(fresh, pos);
    for (MName m:pat){ res= new fearlessFullGrammar.E.Call(res,m,empty(),false,empty(),List.of(), pos); }
    return new XE(x,res);
  }
  @Override public E visitX(fearlessFullGrammar.E.X x){ return new E.X(x.name(),u,x.pos()); }
  @Override public E visitRound(fearlessFullGrammar.E.Round r){ return r.e().accept(this); }
  @Override public E visitImplicit(fearlessFullGrammar.E.Implicit n){  return new E.X(implicits.getLast(),u,n.pos());  }
  @Override public E visitTypedLiteral(fearlessFullGrammar.E.TypedLiteral t){
    var summon= t.l().map(l->l.methods().isEmpty()).orElse(true);
    T.RCC c= visitRCC(t.t());
    if (summon){ return new E.Type(c,u,t.pos()); }
    E.Literal l= visitLiteral(t.l().orElseGet(()->emptyL(t.pos())));
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
    freshF.aliasOwner(this.tops.getLast(), f.apply(c.dec().name()));
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
    return new E.Literal(thisName, ms, u, l.pos());
  }
  @Override public E visitCall(fearlessFullGrammar.E.Call c){
    if (c.pat().isPresent()){ c = desugarCPat(c); }
    if (c.targs().isEmpty()){ return visitICall(c); }
    E e= c.e().accept(this);
    var targs= c.targs().get();
    List<E> es= mapE(c.es());
    List<IT> ts= mapIT(targs.ts());
    return new E.Call(e, c.name(), targs.rc(), ts, es, u, c.pos());
  }
  private Call desugarCPat(Call c){
    var pat= c.pat().get();
    assert c.es().size() == 1;
    fearlessFullGrammar.E par1= c.es().getFirst();
    var fresh= new fearlessFullGrammar.E.X(freshF.freshVar(tops().getLast(), "eqS"),c.pos());    
    fearlessFullGrammar.E res= replaceAtom(par1,fresh);
    par1 = extractAtom(par1);
    var param1= new Parameter(of(pat),empty());
    var param2= new Parameter(of(new XPat.Name(fresh)),empty());
    var sig= new fearlessFullGrammar.Sig(empty(),empty(),empty(),false,List.of(param1,param2),empty());
    var m= new fearlessFullGrammar.M(of(sig),of(res),false,c.pos());
    var par2= new fearlessFullGrammar.E.Literal(empty(),List.of(m),c.pos());
    return new fearlessFullGrammar.E.Call(
      c.e(),c.name(),c.targs(),true,empty(),List.of(par1,par2), c.pos());
  }
  private fearlessFullGrammar.E replaceAtom(fearlessFullGrammar.E par, fearlessFullGrammar.E atom){ return switch(par){
    case fearlessFullGrammar.E.X _ -> atom;
    case fearlessFullGrammar.E.Round _ -> atom;
    case fearlessFullGrammar.E.Literal _ -> atom;
    case fearlessFullGrammar.E.TypedLiteral _ -> atom;
    case fearlessFullGrammar.E.DeclarationLiteral _ -> atom;
    case fearlessFullGrammar.E.Implicit _ -> atom;
    case fearlessFullGrammar.E.Call(var e, var name, var targs, var pars, var pat, var es, var pos) -> 
      new fearlessFullGrammar.E.Call(replaceAtom(e, atom),name,targs,pars, pat, es,pos);
    case fearlessFullGrammar.E.StringInter(var simple, var e, var hashCounts, var strings, var es, var pos) ->
      e.isEmpty()?atom
      :new fearlessFullGrammar.E.StringInter(simple,of(atom),hashCounts,strings,es,pos);
  };}
  private fearlessFullGrammar.E extractAtom(fearlessFullGrammar.E par){ return switch(par){
    case fearlessFullGrammar.E.X e -> e;
    case fearlessFullGrammar.E.Round e -> e;
    case fearlessFullGrammar.E.Literal e -> e;
    case fearlessFullGrammar.E.TypedLiteral e -> e;
    case fearlessFullGrammar.E.DeclarationLiteral e -> e;
    case fearlessFullGrammar.E.Implicit e -> e;
    case fearlessFullGrammar.E.Call e -> extractAtom(e.e());
    case fearlessFullGrammar.E.StringInter e -> e.e().isEmpty()?e: extractAtom(e.e().get());
  };}
  public E visitICall(fearlessFullGrammar.E.Call c){
    E e= c.e().accept(this);
    List<E> es= mapE(c.es());
    return new E.ICall(e, c.name(), es, u, c.pos());
  }
  //TODO: search and replace other cases where we can use typedLiteral
  private fearlessFullGrammar.E.TypedLiteral typedLiteral(String str,Pos p){
    var tn= new TName(str, 0,p);
    var c= new fearlessFullGrammar.T.C(tn,of(List.of()));
    return new fearlessFullGrammar.E.TypedLiteral(new fearlessFullGrammar.T.RCC(empty(),c), empty(), p);    
  }
  @Override public E visitStringInter(fearlessFullGrammar.E.StringInter i){
    String name= i.simple()?"base.SStr":"base.UStr";
    String term= i.simple()?"`":"\"";
    var add= new fearlessFullGrammar.MName(".add",2);
    var build= new fearlessFullGrammar.MName(".build",1);
    var topE= i.e().orElseGet(()->typedLiteral(name+"Procs",i.pos()));
    for (int j= 0; j < i.es().size(); j++){
      var stri= typedLiteral("base."+term+i.strings().get(j)+term,i.pos());
      topE = new fearlessFullGrammar.E.Call(topE,add,empty(),true,empty(),List.of(stri,i.es().get(j)),i.pos());
    }
    var strLast= typedLiteral("base."+term+i.strings().getLast()+term,i.pos());
    var desugared= new fearlessFullGrammar.E.Call(topE,build,empty(),true,empty(),List.of(strLast),i.pos());
    return desugared.accept(this); 
  }  
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