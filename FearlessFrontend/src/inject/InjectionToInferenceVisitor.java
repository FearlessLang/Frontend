package inject;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Stream;

import core.B;
import core.MName;
import core.RC;
import core.Src;
import core.TName;
import core.TSpan;
import utils.OneOr;
import utils.Push;
import utils.Streams;
import fearlessFullGrammar.E.Call;
import fearlessFullGrammar.Parameter;
import fearlessFullGrammar.XPat;
import utils.Pos;
import inference.E;
import inference.IT;
import inference.M;

import static java.util.Optional.*;
import static core.LiteralDeclarations.*;
import static fearlessParser.TokenKind.*;

public record InjectionToInferenceVisitor(Methods meths, TName currentTop, List<String> implicits, Function<TName,TName> f, ArrayList<E.Literal> decs)
{
  static final inference.IT u= IT.U.Instance;
  IT visitT(fearlessFullGrammar.T t){
    return switch (t){
      case fearlessFullGrammar.T.X x -> visitTX(x);
      case fearlessFullGrammar.T.RCX x -> visitRCX(x);
      case fearlessFullGrammar.T.ReadImmX x -> visitReadImmX(x);
      case fearlessFullGrammar.T.RCC c -> visitRCC(c);
    };
  }
  E visitE(fearlessFullGrammar.E e){
    return switch (e){
      case fearlessFullGrammar.E.X x -> visitX(x);
      case fearlessFullGrammar.E.Round r -> visitE(r.e());
      case fearlessFullGrammar.E.Implicit n -> visitImplicit(n);
      case fearlessFullGrammar.E.TypedLiteral t -> visitTypedLiteral(t);
      case fearlessFullGrammar.E.DeclarationLiteral c -> visitDeclarationLiteral(c);
      case fearlessFullGrammar.E.Literal l -> visitLiteral(l);
      case fearlessFullGrammar.E.Call c -> visitCall(c);
    };
  }
  IT.X visitTX(fearlessFullGrammar.T.X x){ return new IT.X(x.name(),x.span()); }
  IT visitReadImmX(fearlessFullGrammar.T.ReadImmX x){ return new IT.ReadImmX(visitTX(x.x())); }
  IT visitRCX(fearlessFullGrammar.T.RCX x){ return new IT.RCX(x.rc(), visitTX(x.x())); }
  IT.RCC visitRCC(fearlessFullGrammar.T.RCC c){
    return new IT.RCC(of(c.rc().orElse(RC.imm)),visitC(c.c()),c.span());
  }
  public IT.C visitC(fearlessFullGrammar.T.C c){
    var tName= c.name();
    var s= tName.s();
    var pr= isPrimitiveLiteral(s);
    if (pr){
      assert tName.pkgName().isEmpty();
      assert tName.arity() == 0;
      var natOutOfRange= isKind(s,UnsignedInt) && !natLiteralInRange(s);
      if (natOutOfRange){ throw meths.p().err().natLiteralOutOfRange(tName); }
      var intOutOfRange= isKind(s,SignedInt) && !intLiteralInRange(s);
      if (intOutOfRange){ throw meths.p().err().intLiteralOutOfRange(tName); }
      var floatNotExact= isKind(s,SignedFloat,UnSignedFloat) && !floatLiteralOk(s);
      if (floatNotExact){ throw meths.p().err().floatLiteralNotExactlyRepresentable(tName); }
    }
    return new IT.C(f.apply(tName),mapT(c.ts().orElse(List.of())));
  }
  List<E> mapE(List<fearlessFullGrammar.E> es){ return es.stream().map(this::visitE).toList(); }
  List<IT> mapT(List<fearlessFullGrammar.T> ts){ return ts.stream().map(this::visitT).toList(); }
  List<IT.C> mapC(List<fearlessFullGrammar.T.C> cs){ return cs.stream().map(this::visitC).toList(); }
  List<B> mapB(List<fearlessFullGrammar.B> bs){ return bs.stream().map(this::visitB).toList(); }
  List<Optional<IT>> mapPT(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(p->p.t().map(this::visitT)).toList(); }
  List<String> mapPX(List<fearlessFullGrammar.Parameter> ps){ return ps.stream().map(this::parameterToName).toList(); }
  String parameterToName(fearlessFullGrammar.Parameter p){
    if (p.xp().isEmpty()){ return "_"; }
    return switch (p.xp().get()){
    case XPat.Name(var x) -> x.name();
    case XPat.Destruct(var _, var _) -> meths.fresh().freshVar(currentTop, "div");
    };
  }
  List<M> mapM(List<fearlessFullGrammar.M> ms){ return ms.stream().map(this::visitM).toList(); }
  M visitM(fearlessFullGrammar.M m){ return new M(visitMSig(m),visitMImpl(m)); }
  M.Sig visitMSig(fearlessFullGrammar.M mm){
    if (mm.sig().isEmpty()){
      List<Optional<IT>> ts= mm.hasImplicit() ? List.of(empty()) : List.of();
      return new M.Sig(empty(),empty(),empty(),ts,empty(),empty(),false,mm.span());
    }
    fearlessFullGrammar.Sig s= mm.sig().get();
    Optional<List<B>> bs= s.bs().map(this::mapB);
    List<Optional<IT>> ts= mapPT(s.parameters());
    if (mm.hasImplicit()){ ts= Push.of(ts,empty()); }
    Optional<IT> res= s.t().map(this::visitT);
    return new M.Sig(s.rc(),s.m(),bs,ts,res,empty(),mm.body().isEmpty(),mm.span());
  }
  public B visitB(fearlessFullGrammar.B b){
    return new B(b.x().name(),switch (b.bt()){
    case fearlessFullGrammar.B.Star()->EnumSet.of(RC.imm,RC.mut,RC.read);
    case fearlessFullGrammar.B.StarStar()->EnumSet.allOf(RC.class);
    case fearlessFullGrammar.B.RCS(List<RC> rcs)-> rcs.isEmpty() ?EnumSet.of(RC.imm) :inOrder(rcs,b.x());
    });
  }
  private EnumSet<RC> inOrder(List<RC> es, fearlessFullGrammar.T.X x){
    var duplicated= es.stream().distinct().count() < es.size();
    if (duplicated){ throw meths.p().err().duplicatedBound(es,x); }
    return EnumSet.copyOf(es);
  }

  Optional<M.Impl> visitMImpl(fearlessFullGrammar.M m){
    if (m.body().isEmpty()){ return empty(); }
    var body= m.body().get();
    var original= m.sig().map(s->s.parameters()).orElse(List.of());
    List<String> ps= mapPX(original);
    List<XE> xpats= xpats(ps,original,m.span());
    if (!xpats.isEmpty()){ body= makeXPatsBody(body,xpats); }
    if (m.hasImplicit()){ var p= meths.fresh().freshVar(currentTop, "impl"); ps= Push.of(ps,p); implicits.add(p); }
    E e= visitE(body);
    if (m.hasImplicit()){ implicits.removeLast(); }
    Optional<MName> name= m.sig().flatMap(s->s.m());
    return of(new M.Impl(name,ps,e));
  }
  private fearlessFullGrammar.E makeXPatsBody(fearlessFullGrammar.E body, List<XE> xes){
    var p= body.pos(); //Block#.let x1={e1}.. .let xn={en}.return{body}
    var span= TSpan.fromPos(p);
    Function<fearlessFullGrammar.E,fearlessFullGrammar.E> k=
      recv->call(recv, ".return", List.of(lambda(body,span)), p);
    for (var xe: xes.reversed()){
      var pat= new XPat.Name(new fearlessFullGrammar.E.X(xe.x, p));
      var thunk= lambda(xe.e, span);
      var k0= k;
      k= recv->callPat(recv, ".let", pat, k0.apply(thunk), p);
    }
    return k.apply(call(typedLiteral("base.Block", body.span(),p), "#",List.of(), p));
  }
  record XE(String x, fearlessFullGrammar.E e){}
  List<XE> xpats(List<String> lowered, List<fearlessFullGrammar.Parameter> original, TSpan span){
    return Streams.zip(lowered, original)
      .flatMap((x,p)->p.xp().stream().flatMap(xp->xp instanceof XPat.Destruct d ? xpat(d,x,span) : Stream.empty()))
      .toList();
  }
  Stream<XE> xpat(XPat.Destruct pat, String fresh, TSpan span){
    return Streams.zip(pat.extract(), pat.parameterNames().toList()).map((e,x)->xpat(e,x,fresh,span));
  }
  XE xpat(List<MName> pat, String x, String fresh, TSpan span){
    fearlessFullGrammar.E res= new fearlessFullGrammar.E.X(fresh, span.pos());
    for (MName m : pat){ res= call(res, m.s(),List.of(), span.pos()); }
    return new XE(x, res);
  }
  private fearlessFullGrammar.E stripRound(fearlessFullGrammar.E e){
    while (e instanceof fearlessFullGrammar.E.Round r){ e= r.e(); }
    return e;
  }
  private E.Literal liftLiteral(Optional<RC> rc,List<IT.C> impl,Optional<String> thisName, List<M> ms, Src src){
    var name= meths.fresh().freshTopType(currentTop,0);
    return new E.Literal(rc,name,List.of(),impl,thisName.orElse("_"), ms,src,true);
  }
  private E visitReceiver(fearlessFullGrammar.E e){
    if (!(stripRound(e) instanceof fearlessFullGrammar.E.Literal ol)){ return visitE(e); }
    var l= visitLiteral(ol);
    decs.add(l);
    return l;
  }
  //Here new FreeXs().ftvMs(ms) is all since by construction no Cs and no inferred type;
  E.Literal visitLiteral(fearlessFullGrammar.E.Literal l){
    var ms= mapM(l.methods());
    var name= l.thisName().map(n->n.name());
    return liftLiteral(empty(),List.of(),name,ms,new Src(l));
  }
  E visitX(fearlessFullGrammar.E.X x){ return new E.X(x.name(),new Src(x)); }
  E visitImplicit(fearlessFullGrammar.E.Implicit n){ return new E.X(implicits.getLast(),new Src(n)); }
  E visitTypedLiteral(fearlessFullGrammar.E.TypedLiteral t){
    if (t.l().isEmpty()){ return new E.Type(visitRCC(t.t()),new Src(t)); }
    List<IT.C> impl= List.of(visitC(t.t().c()));
    var ms= mapM(t.l().get().methods());
    E.Literal l= liftLiteral(of(t.t().rc().orElse(RC.imm)),impl,t.l().get().thisName().map(n->n.name()), ms,new Src(t));
    decs.add(l);
    return l;
  }
  E visitDeclarationLiteral(fearlessFullGrammar.E.DeclarationLiteral c){
    var name= f.apply(c.dec().name());
    meths.fresh().aliasOwner(currentTop,name);
    return addDeclaration(name, c.rc().orElse(RC.imm),c.dec(),false);
  }
  public E.Literal addDeclaration(TName name,RC rc,fearlessFullGrammar.Declaration d, boolean top){
    String thisName= d.l().thisName().map(n->n.name()).orElseGet(()->top?"this":"_");
    List<B> bs= d.bs().map(this::mapB).orElse(List.of());
    List<IT.C> cs= mapC(d.cs());
    List<M> ms= mapM(d.l().methods());
    E.Literal l= new E.Literal(of(rc),name,bs,cs,thisName, ms, new Src(d),false);
    decs.add(l);
    return l;
  }
  E visitCall(fearlessFullGrammar.E.Call c){
    if (c.pat().isPresent()){ c= desugarCPat(c); }
    if (c.targs().isEmpty()){ return visitICall(c); }
    E e= visitReceiver(c.e());
    var targs= c.targs().get();
    List<E> es= mapE(c.es());
    return new E.Call(e, c.name(), targs.rc(), mapT(targs.ts()), es, new Src(c));
  }
  private Call desugarCPat(Call c){
    var pat= c.pat().get();
    fearlessFullGrammar.E par1= OneOr.of("Equals sugar has one argument",c.es().stream());
    var fresh= new fearlessFullGrammar.E.X(meths.fresh().freshVar(currentTop, "eqS"),c.pos());
    fearlessFullGrammar.E res= replaceAtom(par1,fresh);
    par1= extractAtom(par1);
    var param1= new Parameter(of(pat),empty());
    var param2= new Parameter(of(new XPat.Name(fresh)),empty());
    var sig= new fearlessFullGrammar.Sig(empty(),empty(),empty(),false,List.of(param1,param2),empty());
    var m= new fearlessFullGrammar.M(of(sig),of(res),false,c.span());
    var par2= new fearlessFullGrammar.E.Literal(empty(),List.of(m),c.span());
    return new fearlessFullGrammar.E.Call(
      c.e(),c.name(),c.targs(),true,empty(),List.of(par1,par2), c.pos());
  }
  private fearlessFullGrammar.E replaceAtom(fearlessFullGrammar.E par, fearlessFullGrammar.E atom){
    if (!(par instanceof fearlessFullGrammar.E.Call c)){ return atom; }
    return new fearlessFullGrammar.E.Call(replaceAtom(c.e(),atom),c.name(),c.targs(),c.pars(),c.pat(),c.es(),c.pos());
  }
  private fearlessFullGrammar.E extractAtom(fearlessFullGrammar.E par){
    while (par instanceof fearlessFullGrammar.E.Call c){ par= c.e(); }
    return par;
  }
  public E visitICall(fearlessFullGrammar.E.Call c){ return new E.ICall(visitReceiver(c.e()), c.name(), mapE(c.es()), new Src(c)); }
  private fearlessFullGrammar.E.TypedLiteral typedLiteral(String str,TSpan s,Pos p){
    var tn= new TName(str, 0,p);
    var c= new fearlessFullGrammar.T.C(tn,of(List.of()));
    return new fearlessFullGrammar.E.TypedLiteral(new fearlessFullGrammar.T.RCC(empty(),c,s), empty(), p);
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
}