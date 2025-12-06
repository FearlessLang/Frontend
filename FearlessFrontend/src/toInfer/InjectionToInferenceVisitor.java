package toInfer;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.B;
import core.Src;
import utils.Bug;
import utils.Push;
import fearlessFullGrammar.E.Call;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.Parameter;
import fearlessFullGrammar.XPat;
import fearlessParser.RC;
import files.Pos;
import inference.E;
import inference.IT;
import inference.M;
import inject.Methods;
import message.WellFormednessErrors;
import naming.FreshPrefix;
import pkgmerge.OtherPackages;
import pkgmerge.Package;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;

import static java.util.Optional.*;

import java.util.ArrayList;

public record InjectionToInferenceVisitor(Methods meths, TName currentTop, List<String> implicits, Function<TName,TName> f, ArrayList<E.Literal> decs, Package pkg, List<List<B>> bsInScope, OtherPackages other, FreshPrefix freshF)
    implements fearlessFullGrammar.EVisitor<inference.E>,fearlessFullGrammar.TVisitor<IT>{
  static final inference.IT u= IT.U.Instance;
  static fearlessFullGrammar.E.Literal emptyL(Pos pos){ return new fearlessFullGrammar.E.Literal(empty(),List.of(),TSpan.fromPos(pos)); }
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
    if ( p.xp().isEmpty()){ return "_"; }
    XPat xp= p.xp().get();
    return switch (xp){
    case XPat.Name(var x) -> x.name();
    case XPat.Destruct(var _, var _) -> freshF.freshVar(currentTop, "div");
    };
  } 
  List<M> mapM(List<fearlessFullGrammar.M> ms){ return ms.stream().map(this::visitM).toList(); } 
  M visitM(fearlessFullGrammar.M m){ return new M(visitMSig(m),visitMImpl(m)); }
  M.Sig visitMSig(fearlessFullGrammar.M mm){
    if (mm.sig().isEmpty()){
      List<Optional<IT>> ts= !mm.hasImplicit()?List.of():List.of(empty());
      return new M.Sig(empty(),empty(),empty(),ts,empty(),empty(),false,mm.span()); 
    }
    fearlessFullGrammar.Sig s= mm.sig().get();
    Optional<List<B>> bs= s.bs().map(this::mapB);
    List<Optional<IT>> ts= mapPT(s.parameters());
    if (mm.hasImplicit()){ ts= Push.of(ts,empty()); }
    Optional<IT> res= s.t().map(ti->ti.accept(this));
    return new M.Sig(s.rc(),s.m(),bs,ts,res,empty(),mm.body().isEmpty(),mm.span());
  }
  public B visitB(fearlessFullGrammar.B b){
    return new B(b.x().name(),switch (b.bt()){
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
    List<XE> xpats= xpats(ps,original,m.span());
    if (!xpats.isEmpty()){ body = makeXPatsBody(body,xpats); }
    if (m.hasImplicit()){ var p= freshF.freshVar(currentTop, "impl"); ps = Push.of(ps,p); implicits.add(p); }
    E e= body.accept(this);
    m.sig().ifPresent(_->bsInScope.removeLast());
    if (m.hasImplicit()){ implicits.removeLast(); }
    Optional<MName> name= m.sig().flatMap(s->s.m());
    return of(new M.Impl(name,ps,e));
  }
  private fearlessFullGrammar.E makeXPatsBody(fearlessFullGrammar.E body, List<XE> xes){
    var p= body.pos(); //Block#.let x1={e1}.. .let xn={en}.return{body}
    var block= call(typedLiteral("base.Block", p), "#",List.of(), p);
    for (var xe : xes){
      var pat= new XPat.Name(new fearlessFullGrammar.E.X(xe.x, p));
      block= callPat(block, ".let", pat, lambda(xe.e, TSpan.fromPos(p)), p);
    }
    return call(block, ".return", List.of(lambda(body,TSpan.fromPos(p))), p);
  }
  record XE(String x, fearlessFullGrammar.E e){}
  boolean isXPat(fearlessFullGrammar.Parameter p){
    return p.xp().isPresent() && p.xp().get() instanceof XPat.Destruct; 
  }
  List<XE> xpats(List<String> lowered, List<fearlessFullGrammar.Parameter> original, TSpan span){
    assert lowered.size() == original.size();
    return IntStream.range(0,lowered.size()).boxed()
      .filter(i->isXPat(original.get(i)))
      .flatMap(i->xpat((XPat.Destruct)original.get(i).xp().get(),lowered.get(i),span))
      .toList();
  }
  Stream<XE> xpat(XPat.Destruct pat, String fresh, TSpan span){
    List<String> patterns = pat.parameterNames().toList();
    assert pat.extract().size() == patterns.size();
    return IntStream.range(0,patterns.size())
      .mapToObj(i->xpat(pat.extract().get(i),patterns.get(i),fresh,span));
  }
  XE xpat(List<MName> pat, String x, String fresh, TSpan span){
    fearlessFullGrammar.E res= new fearlessFullGrammar.E.X(fresh, span.pos());
    for (MName m : pat) { res= call(res, m.s(),List.of(), span.pos()); }
    return new XE(x, res);
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
  //TODO: check if now the stream is always empty
  private E.Literal liftLiteral(Optional<RC> rc,Stream<String> bs,List<IT.C> impl,Optional<String> thisName, List<M> ms, Src src){
    var _bs= bs.distinct().map(this::xB).toList();
    var name= freshF.freshTopType(currentTop,_bs.size());
    return new E.Literal(rc,name,_bs,impl,thisName.orElse("_"), ms,src);
  }
  private E visitReceiver(fearlessFullGrammar.E e){
    var ol= asLambdaReceiver(e);
    if (ol.isEmpty()){ return e.accept(this); }
    var ms= mapM(ol.get().methods());
    var name= ol.get().thisName().map(n->n.name());
    //Here new FreeXs().ftvMs(ms) is all since by construction no Cs and no inferred type;
    var l= liftLiteral(Optional.of(RC.imm),Stream.of(),List.of(),name,ms,new Src(ol.get()));
    decs.add(l);
    return l;
  }
  @Override public E.Literal visitLiteral(fearlessFullGrammar.E.Literal l){ 
    var ms= mapM(l.methods());
    var name= l.thisName().map(n->n.name());
    return liftLiteral(Optional.empty(),Stream.of(),List.of(),name,ms,new Src(l));
  }
  @Override public E visitX(fearlessFullGrammar.E.X x){ return new E.X(x.name(),new Src(x)); }
  @Override public E visitRound(fearlessFullGrammar.E.Round r){ return r.e().accept(this); }
  @Override public E visitImplicit(fearlessFullGrammar.E.Implicit n){ return new E.X(implicits.getLast(),new Src(n)); }
  @Override public E visitTypedLiteral(fearlessFullGrammar.E.TypedLiteral t){
    if (t.l().isEmpty()){ return new E.Type(visitRCC(t.t()),new Src(t)); }
    List<IT.C> impl= List.of(visitC(t.t().c()));
    List<fearlessFullGrammar.M> ms0= t.l().map(l->l.methods()).orElse(List.of());
    Optional<String> thisName= t.l().flatMap(l->l.thisName().map(n->n.name()));
    var ms= mapM(ms0);
    //Stream<String> bs= Stream.concat(
    //  new FreeXs().ftvMs(ms),new FreeXs().ftvT(visitRCC(t.t())));
    E.Literal l= liftLiteral(Optional.of(t.t().rc().orElse(RC.imm)),Stream.of(),impl,thisName, ms,new Src(t));
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
    E.Literal l= new E.Literal(Optional.of(rc),name,bs,cs,thisName, ms, new Src(d.l()));
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
    return new E.Call(e, c.name(), targs.rc(), ts, es, new Src(c));
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
    var m= new fearlessFullGrammar.M(of(sig),of(res),false,c.span());
    var par2= new fearlessFullGrammar.E.Literal(empty(),List.of(m),c.span());
    return new fearlessFullGrammar.E.Call(
      c.e(),c.name(),c.targs(),true,empty(),List.of(par1,par2), c.pos());
  }
  private fearlessFullGrammar.E replaceAtom(fearlessFullGrammar.E par, fearlessFullGrammar.E atom){ return switch (par){
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
  private fearlessFullGrammar.E extractAtom(fearlessFullGrammar.E par){ return switch (par){
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
    return new E.ICall(e, c.name(), es, new Src(c));
  }
  private fearlessFullGrammar.E.TypedLiteral typedLiteral(String str,Pos p){
    var tn= new TName(str, 0,p);
    var c= new fearlessFullGrammar.T.C(tn,of(List.of()));
    return new fearlessFullGrammar.E.TypedLiteral(new fearlessFullGrammar.T.RCC(empty(),c), empty(), p);    
  }
  private fearlessFullGrammar.E lambda(fearlessFullGrammar.E body, TSpan span){
    return new fearlessFullGrammar.E.Literal(empty(), List.of(new fearlessFullGrammar.M(empty(), of(body), false, span)), span);
  }
  private fearlessFullGrammar.E call(fearlessFullGrammar.E e, String m, List<fearlessFullGrammar.E> args, Pos p){
    return new fearlessFullGrammar.E.Call(e, new MName(m, args.size()), empty(), true, empty(), args, p);
  }
  private fearlessFullGrammar.E callPat(fearlessFullGrammar.E e, String m, XPat pat, fearlessFullGrammar.E a, Pos p){
    return new fearlessFullGrammar.E.Call(e, new MName(m, 2), empty(), true, of(pat), List.of(a), p);
  }
  @Override public E visitStringInter(fearlessFullGrammar.E.StringInter i){
    String name= i.simple() ? "base.SStr" : "base.UStr";
    String q= i.simple() ? "`" : "\"";
    var top= i.e().orElseGet(() -> typedLiteral(name + "Procs", i.pos()));
    for (int j= 0; j < i.es().size(); j++) {
      var s= typedLiteral("base." + q + i.strings().get(j) + q, i.pos());
      top= call(top, ".add", List.of(s,i.es().get(j)), i.pos());
    }
    var end= typedLiteral("base." + q + i.strings().getLast() + q, i.pos());
    return call(top, ".build", List.of(end), i.pos()).accept(this);
  }
}