package toInfer;

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
import inference.B;
import inference.E;
import inference.IT;
import inference.M;
import inject.Methods;
import message.WellFormednessErrors;
import naming.FreshPrefix;
import pkgmerge.OtherPackages;
import pkgmerge.Package;
import fearlessFullGrammar.TName;
import static java.util.Optional.*;

public record InjectionToInferenceVisitor(Methods meths, TName currentTop, List<String> implicits, Function<TName,TName> f, List<E.Literal> decs, Package pkg, List<List<B>> bsInScope, OtherPackages other, FreshPrefix freshF)
    implements fearlessFullGrammar.EVisitor<inference.E>,fearlessFullGrammar.TVisitor<IT>{
  static final inference.IT u= IT.U.Instance;
  static fearlessFullGrammar.E.Literal emptyL(Pos pos){ return new fearlessFullGrammar.E.Literal(empty(),List.of(),pos); }
  @Override public IT.X visitTX(fearlessFullGrammar.T.X x){ return new IT.X(x.name()); }
  @Override public IT visitReadImmX(fearlessFullGrammar.T.ReadImmX x){ return new IT.ReadImmX(visitTX(x.x())); }
  @Override public IT visitRCX(fearlessFullGrammar.T.RCX x){ return new IT.RCX(x.rc(), visitTX(x.x())); }
  @Override public IT.RCC visitRCC(fearlessFullGrammar.T.RCC c){
    return new IT.RCC(c.rc().orElse(RC.imm),visitC(c.c()));
  }
  public IT.C visitC(fearlessFullGrammar.T.C c){
    var tName= c.name();
    var tNameMap= f.apply(tName);
    var ts= c.ts().orElse(List.of());
    return new IT.C(tNameMap,mapT(ts));
  }
  List<E> mapE(List<fearlessFullGrammar.E> es){ return es.stream().map(e->e.accept(this)).toList(); }
  List<IT> mapT(List<fearlessFullGrammar.T> ts){ return ts.stream().map(t->t.accept(this)).toList(); }
  List<IT.C> mapC(List<fearlessFullGrammar.T.C> cs){ return cs.stream().map(t->visitC(t)).toList(); }
  List<B> mapB(List<fearlessFullGrammar.B> bs){ return bs.stream().map(b->visitB(b)).toList(); }
  List<Optional<IT>> mapPT(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(p->p.t().map(ti->ti.accept(this))).toList(); }
  List<String> mapPX(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(this::parameterToName).toList(); }
  String parameterToName(fearlessFullGrammar.Parameter p){
    if( p.xp().isEmpty()){ return "_"; }
    XPat xp= p.xp().get();
    return switch(xp){
    case XPat.Name(var x) -> x.name();
    case XPat.Destruct(var _, var _) -> freshF.freshVar(currentTop, "div");
    };
  }  
  List<M> mapM(List<fearlessFullGrammar.M> ms){ return ms.stream().map(this::visitM).toList(); }
  M visitM(fearlessFullGrammar.M m){ return new M(visitMSig(m),visitMImpl(m)); }
  M.Sig visitMSig(fearlessFullGrammar.M mm){
    if(mm.sig().isEmpty()){
      List<Optional<IT>> ts= !mm.hasImplicit()?List.of():List.of(empty());
      return new M.Sig(empty(),empty(),empty(),ts,empty(),empty(),false,mm.pos()); 
    }
    fearlessFullGrammar.Sig s= mm.sig().get();
    Optional<List<B>> bs= s.bs().map(this::mapB);
    List<Optional<IT>> ts= mapPT(s.parameters());
    if (mm.hasImplicit()){ ts= Push.of(ts,empty()); }
    Optional<IT> res= s.t().map(ti->ti.accept(this));
    return new M.Sig(s.rc(),s.m(),bs,ts,res,empty(),mm.body().isEmpty(),mm.pos());
  }
  public B visitB(fearlessFullGrammar.B b){
    return new B(b.x().name(),switch(b.bt()){
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
    if (m.hasImplicit()){ var p= freshF.freshVar(currentTop, "impl"); ps = Push.of(ps,p); implicits.add(p); }
    E e= body.accept(this);
    m.sig().ifPresent(_->bsInScope.removeLast());
    if (m.hasImplicit()){ implicits.removeLast(); }
    Optional<MName> name= m.sig().flatMap(s->s.m());
    return of(new M.Impl(name,ps,e));
  }
  private fearlessFullGrammar.E makeXPatsBody(fearlessFullGrammar.E body, List<XE> xes){
    var p= body.pos();
    //Block#.let x1={e1}.. .let xn={en}.return{body}
    fearlessFullGrammar.E blockE=typedLiteral("base.Block",p); 
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
  private fearlessFullGrammar.E stripRound(fearlessFullGrammar.E e){
    while (e instanceof fearlessFullGrammar.E.Round r){ e = r.e(); }
    return e;
  }
  private Optional<fearlessFullGrammar.E.Literal> asLambdaReceiver(fearlessFullGrammar.E e){
    e = stripRound(e);
    if (e instanceof fearlessFullGrammar.E.Literal l){ return Optional.of(l); }
    return Optional.empty();
  }
  private E.Literal liftLiteral(Optional<RC> rc,Stream<String> bs,List<IT.C> impl,Optional<String> thisName, List<M> ms, Pos pos){
    var _bs= bs.distinct().map(this::xB).toList();
    var name= freshF.freshTopType(currentTop,_bs.size());
    return new E.Literal(rc,name,_bs,impl,thisName.orElse("_"), ms,pos);
  }
  private E visitReceiver(fearlessFullGrammar.E e){
    var ol= asLambdaReceiver(e);
    if (ol.isEmpty()){ return e.accept(this); }
    var ms= mapM(ol.get().methods());
    var name= ol.get().thisName().map(n->n.name());
    var l= liftLiteral(Optional.of(RC.imm),new FreeXs().ftvMs(ms),List.of(),name,ms,ol.get().pos());
    decs.add(l);
    return l;
  }
  @Override public E.Literal visitLiteral(fearlessFullGrammar.E.Literal l){ 
    var ms= mapM(l.methods());
    var name= l.thisName().map(n->n.name());
    return liftLiteral(Optional.empty(),new FreeXs().ftvMs(ms),List.of(),name,ms,l.pos());
  }
  @Override public E visitX(fearlessFullGrammar.E.X x){ return new E.X(x.name(),x.pos()); }
  @Override public E visitRound(fearlessFullGrammar.E.Round r){ return r.e().accept(this); }
  @Override public E visitImplicit(fearlessFullGrammar.E.Implicit n){  return new E.X(implicits.getLast(),n.pos());  }
  @Override public E visitTypedLiteral(fearlessFullGrammar.E.TypedLiteral t){
    if (t.l().isEmpty()){ return new E.Type(visitRCC(t.t()),t.pos()); }
    List<IT.C> impl= List.of(visitC(t.t().c()));
    List<fearlessFullGrammar.M> ms0= t.l().map(l->l.methods()).orElse(List.of());
    Optional<String> thisName= t.l().flatMap(l->l.thisName().map(n->n.name()));
    var ms= mapM(ms0);
    Stream<String> bs= Stream.concat(
      new FreeXs().ftvMs(ms),new FreeXs().ftvT(visitRCC(t.t())));
    E.Literal l= liftLiteral(Optional.of(t.t().rc().orElse(RC.imm)),bs,impl,thisName, ms,t.pos());
    decs.add(l);
    return l;
  }
  B xB(String x){
    return bsInScope.stream()
      .flatMap(List::stream)
      .filter(b->b.x().equals(x)).findFirst()
      .orElseThrow(() -> Bug.of("Free type variable " + x + " not in bsInScope"));
  }  
  @Override public E visitDeclarationLiteral(fearlessFullGrammar.E.DeclarationLiteral c){
    freshF.aliasOwner(currentTop, f.apply(c.dec().name()));
    return addDeclaration(f.apply(c.dec().name()), c.rc().orElse(RC.imm),c.dec(),false);
  }
  public E.Literal addDeclaration(TName name,RC rc,fearlessFullGrammar.Declaration d, boolean top){
    String thisName= d.l().thisName().map(n->n.name()).orElseGet(()->top?"this":"_");
    List<B> bs= d.bs().map(this::mapB).orElse(List.of());
    bsInScope.add(bs);
    List<IT.C> cs= mapC(d.cs());    
    List<M> ms= mapM(d.l().methods());
    E.Literal l= new E.Literal(Optional.of(rc),name,bs,cs,thisName, ms, d.l().pos());      
    decs.add(l);
    bsInScope.removeLast();
    return l;
  }
  @Override public E visitCall(fearlessFullGrammar.E.Call c){
    if (c.pat().isPresent()){ c = desugarCPat(c); }
    if (c.targs().isEmpty()){ return visitICall(c); }
    E e= visitReceiver(c.e());
    var targs= c.targs().get();
    List<E> es= mapE(c.es());
    List<IT> ts= mapT(targs.ts());
    return new E.Call(e, c.name(), targs.rc(), ts, es, c.pos());
  }
  private Call desugarCPat(Call c){
    var pat= c.pat().get();
    assert c.es().size() == 1;
    fearlessFullGrammar.E par1= c.es().getFirst();
    var fresh= new fearlessFullGrammar.E.X(freshF.freshVar(currentTop, "eqS"),c.pos());    
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
    E e= visitReceiver(c.e());
    List<E> es= mapE(c.es());
    return new E.ICall(e, c.name(), es, c.pos());
  }
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
}