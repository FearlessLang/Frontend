package inject;

import java.util.*;
import java.util.stream.Stream;

import core.B;
import core.LiteralDeclarations;
import core.MName;
import core.RC;
import core.Src;
import core.T;
import core.TName;
import core.TSpan;
import inference.Gamma;
import inference.IT;
import offensiveUtils.EqTransparent;
import typeSystem.TypeSystem;
import utils.Bug;
import utils.OneOr;
import utils.Pos;
import utils.Push;
import utils.Streams;

public record ToCore(List<B> ctx){
  core.E of(inference.E exp, inference.E orig){ return switch (exp){
    case inference.E.X(var name, _, var src, _) -> new core.E.X(name,src);
    case inference.E.Type(var type, _, var src, _) -> type(type,src);
    case inference.E.Literal le -> literal(le,orig);
    case inference.E.Call ce -> call(ce,callLike(orig,ce.name()));
    case inference.E.ICall ic -> callFromICall(ic,callLike(orig,ic.name()));
  };}
  private boolean inScope(List<IT> ts){ return ts.stream().flatMap(IT::ftv).allMatch(B.xs(ctx)::contains); }
  core.E.Type type(IT.RCC type, Src src){
    assert inScope(List.of(type));
    return new core.E.Type(new T.RCC(type.rc().orElse(RC.imm),TypeRename.itcToTC(type.c()),type.span()),src);
  }
  core.E.Literal literal(inference.E.Literal e, inference.E orig){
    var o= (inference.E.Literal)orig;
    assert o.src() == e.src();
    var rc= o.rc().or(e::rc).orElse(RC.imm);
    assert o.infName() == e.infName();
    assert o.infName() || e.name().equals(o.name());
    assert e.thisName().equals(o.thisName());
    var oBs= originalBs(o);
    assert oBs.isEmpty() || !o.infName();
    var bs= oBs.orElse(e.bs());
    var uncommitted= e.infName() && bs.isEmpty();
    if (uncommitted){
      var free= new FreeXs(new Gamma());
      bs= Streams.of(free.ftvCs(e.cs()),free.ftvMs(e.ms()),free.ftvMs(o.ms())).distinct().map(x->B.get(ctx,x)).toList();
    }
    assert !e.infName() || B.xs(ctx).containsAll(B.xs(bs));
    var name= e.name().withArity(bs.size());
    var inner= new ToCore(e.infName() ? Push.of(ctx,bs).stream().distinct().toList() : bs);
    var ms= inner.mapMs(e.ms(),o.ms()).stream().map(m->withOrigin(m,e.name(),name)).toList();
    var cs= TypeRename.itcToTC(distinctTypes(inner.ctx(),o.cs().isEmpty() ? e.cs() : Push.of(o.cs(),e.cs())));
    assert InjectionToInferenceVisitor.duplicatedSupertypes(inner.ctx(),cs).isEmpty();
    return new core.E.Literal(rc,name,bs,cs,e.thisName(),ms,e.src(),e.infName());
  }
  static List<IT.C> distinctTypes(List<B> bs, List<IT.C> cs){
    var res= new ArrayList<IT.C>();
    for (var c : cs){ if (res.stream().noneMatch(r->sameType(bs,r,c))){ res.add(c); } }
    return Collections.unmodifiableList(res);
  }
  private static boolean sameType(List<B> bs, IT.C a, IT.C b){
    var span= TSpan.fromPos(Pos.unknown);
    return TypeSystem.eqModXRC(bs,new T.RCC(RC.imm,TypeRename.itcToTC(a),span),new T.RCC(RC.imm,TypeRename.itcToTC(b),span));
  }
  private static core.M withOrigin(core.M m, TName from, TName to){
    var s= m.sig();
    if (!s.origin().equals(from)){ return m; }
    return m.withSig(new core.Sig(s.rc(),s.m(),s.bs(),s.ts(),s.ret(),to,s.abs(),s.span()));
  }
  Optional<List<B>> originalBs(inference.E.Literal o){
    var explicit= switch (o.src().inner){
      case fearlessFullGrammar.E.TypedLiteral _ -> false; //Not tl.t().c().ts().isPresent(): this would be about the first eventual c in cs; not the anon heir
      case fearlessFullGrammar.E.Literal _ -> false;
      case fearlessFullGrammar.Declaration(_, var bs, _, _) -> bs.isPresent();
      default -> throw Bug.of(o.src().inner.getClass().getName());
    };
    return explicit ? Optional.of(o.bs()) : Optional.empty();
  }

  private List<core.E> mapArgs(List<inference.E> es, List<inference.E> oEs){ return Streams.zip(es,oEs).map(this::of).toList(); }
  core.E.Call call(inference.E.Call e, CallLike o){
    var rc= o.rc.or(e::rc).orElse(RC.imm);
    var targs= o.targs.isEmpty() ? e.targs() : o.targs;
    assert inScope(targs);
    return new core.E.Call(of(e.e(),o.e),e.name(),rc,TypeRename.itToT(targs),mapArgs(e.es(),o.es),new EqTransparent<>(TypeRename.itToT(e.t())),e.src());
  }
  core.E.Call callFromICall(inference.E.ICall e, CallLike o){
    assert o.rc.isEmpty();
    assert o.targs.isEmpty();
    return new core.E.Call(of(e.e(),o.e),e.name(),RC.imm,List.of(),mapArgs(e.es(),o.es),new EqTransparent<>(TypeRename.itToT(e.t())),e.src());
  }
  private List<core.M> mapMs(List<inference.M> es, List<inference.M> os){
    return es.stream()
      .map(me->m(me,me.impl().isEmpty() ? me : matchM(os,me)))
      .toList();
  }
  private static inference.M matchM(List<inference.M> os, inference.M e){
    var s= e.sig().span();
    return OneOr.of("Failing to connect methods @"+s, os.stream().filter(o->o.sig().span() == s));
  }
  private core.M m(inference.M e, inference.M o){
    var s= sig(e.sig(), o.sig());
    if (e.impl().isEmpty()){
      assert o.impl().isEmpty();
      return new core.M(s,nUnderscores(s.ts().size()),Optional.empty());
    }
    var ei= e.impl().get();
    var oi= o.impl().get();
    var inner= new ToCore(Push.of(ctx,s.bs()).stream().distinct().toList());
    return new core.M(s,ei.xs(),Optional.of(inner.of(ei.e(),oi.e())));
  }
  core.Sig sig(inference.M.Sig inf, inference.M.Sig usr){
    var ts= Streams.zip(usr.ts(),inf.ts()).map((u,i)->u.or(()->i)).toList();
    var ret= usr.ret().or(inf::ret);
    var rc= usr.rc().or(inf::rc).orElse(RC.imm);
    var m= usr.m().or(inf::m).orElse(new MName(".inferenceFailed", ts.size()));
    var bs= usr.bs().or(inf::bs).orElse(List.of());
    var origin= usr.origin().or(inf::origin).orElse(LiteralDeclarations.inferUnknown);
    return new core.Sig(rc,m,bs,ts.stream().map(TypeRename::itToT).toList(),TypeRename.itToT(ret),origin,usr.abs(),usr.span());
  }
  private record CallLike(inference.E e,List<inference.E> es,Optional<RC> rc,List<IT> targs){}
  private static CallLike callLike(inference.E o,MName name){
    return switch (o){
      case inference.E.Call(var e, var n, var rc, var targs, var es, _, _, _) when n.equals(name) -> new CallLike(e,es,rc,targs);
      case inference.E.ICall(var e, var n, var es, _, _, _) when n.equals(name) -> new CallLike(e,es,Optional.empty(),List.of());
      default -> throw Bug.unreachable();
    };
  }
  private List<String> nUnderscores(int n){ return Stream.generate(()->"_").limit(n).toList(); }

  private static final Optional<core.E> syntheticBody= Optional.of(new core.E.X("this",Src.synthetic));
  core.M mSynthetic(inference.M m){
    var s= sig(m.sig(),m.sig());
    if (m.impl().isEmpty()){ return new core.M(s,nUnderscores(s.ts().size()),Optional.empty()); }
    return new core.M(s,m.impl().get().xs(),syntheticBody);
  }
}