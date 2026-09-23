package inject;

import java.util.*;
import java.util.stream.Stream;

import core.B;
import core.E;
import core.MName;
import core.RC;
import core.Src;
import core.T;
import inference.IT;
import offensiveUtils.EqTransparent;
import utils.Bug;
import utils.OneOr;
import utils.Streams;

public class ToCore{
  core.E of(inference.E exp, inference.E orig){ return switch (exp){
    case inference.E.X(var name, _, Src src, _) -> new core.E.X(name,src);
    case inference.E.Type(var type, _, Src src, _) -> type(type,src);
    case inference.E.Literal le -> literal(le,litLike(orig,le));
    case inference.E.Call ce -> call(ce,callLike(orig,ce.name()));
    case inference.E.ICall ic -> callFromICall(ic,callLike(orig,ic.name()));
  };}
  core.E.Type type(IT.RCC type, Src src){ return new core.E.Type(new T.RCC(type.rc().orElse(RC.imm),TypeRename.itcToTC(type.c()),type.span()),src); }
  core.E.Literal literal(inference.E.Literal e, inference.E.Literal o){
    var rc= o.rc().orElse(e.rc().orElse(RC.imm));
    var ms= mapMs(e.ms(),o.ms());
    assert o.infName() == e.infName();
    assert o.infName() || e.name().equals(o.name());
    assert e.thisName().equals(o.thisName());
    var oBs= originalBs(o);
    assert oBs.isEmpty() || !o.infName():
     o.infName()+" "+oBs;
    var bs= oBs.orElse(e.bs());
    var cs= TypeRename.itcToTC(o.cs().isEmpty()?e.cs():Stream.concat(o.cs().stream(),e.cs().stream()).distinct().toList());
    return new core.E.Literal(rc,e.name(),bs,cs,e.thisName(),ms,e.src(),e.infName());
  }
  Optional<List<B>> originalBs(inference.E.Literal o){
    boolean explicit= switch (o.src().inner){
      case fearlessFullGrammar.E.TypedLiteral _->false; //Not tl.t().c().ts().isPresent(): this would be about the first eventual c in cs; not the anon heir
      case fearlessFullGrammar.E.Literal _->false;
      case fearlessFullGrammar.E.DeclarationLiteral dl->dl.dec().bs().isPresent();
      case fearlessFullGrammar.Declaration dec->dec.bs().isPresent();
      default -> throw Bug.of(o.src().inner.getClass().getName()); 
      };
    return explicit ? Optional.of(o.bs()) : Optional.empty();
    }
  
  private List<core.E> mapArgs(List<inference.E> es, List<inference.E> oEs){ return Streams.zip(es,oEs).map(this::of).toList(); }
  core.E.Call call(inference.E.Call e, CallLike o){
    var rc= o.rc.orElse(e.rc().orElse(RC.imm));
    var targs= !o.targs.isEmpty() ? o.targs : e.targs();
    var recv= of(e.e(),o.e);
    var args= mapArgs(e.es(),o.es);
    return new core.E.Call(recv,e.name(),rc,TypeRename.itToT(targs),args,new EqTransparent<>(TypeRename.itToT(e.t())),e.src());
  }
  core.E.Call callFromICall(inference.E.ICall e, CallLike o){
    assert o.rc.isEmpty();
    assert o.targs.isEmpty();
    var recv= of(e.e(),o.e);
    var args= mapArgs(e.es(),o.es);
    return new core.E.Call(recv,e.name(),RC.imm,List.of(),args,new EqTransparent<>(TypeRename.itToT(e.t())),e.src());
  }
  private List<core.M> mapMs(List<inference.M> es, List<inference.M> os){
    return es.stream()
      .map(me->me.impl().isEmpty()? m(me,me) : m(me,matchM(os,me)))
      .toList();
  }
  private static inference.M matchM(List<inference.M> os, inference.M e){
    var s= e.sig().span();
    return OneOr.of("failing to connect methods @"+s, os.stream().filter(o->o.sig().span()==s));
  }
  private core.M m(inference.M e, inference.M o){
    var s= sig(e.sig(), o.sig());
    if (e.impl().isEmpty()){
      assert o.impl().isEmpty();
      return new core.M(s,nUnderscores(s.ts().size()),Optional.empty());
    }
    assert o.impl().isPresent();
    var ei= e.impl().get();
    var oi= o.impl().get();
    return new core.M(s,ei.xs(),Optional.of(of(ei.e(),oi.e())));
  }
  core.Sig sig(inference.M.Sig inf, inference.M.Sig usr){
    var ts= Streams.zip(usr.ts(),inf.ts()).map((u,i)->u.or(()->i)).toList();
    var ret= usr.ret().isEmpty() ? inf.ret() : usr.ret();
    var rc= usr.rc().orElse(inf.rc().orElse(RC.imm));
    var m= usr.m().orElse(inf.m().orElse(new MName(".inferenceFailed", ts.size())));
    var bs= usr.bs().orElse(inf.bs().orElse(List.of()));
    var origin= usr.origin().orElse(inf.origin().orElse(TypeRename.inferUnknown.c().name()));
    return new core.Sig(rc,m,bs,TypeRename.itOptToT(ts),TypeRename.itToT(ret),origin,usr.abs(),usr.span());
  }
  private static inference.E.Literal litLike(inference.E o,inference.E.Literal e){
    var ol=(inference.E.Literal)o;
    assert ol.name().s().equals(e.name().s()): ol.name() + " " + e.name();
    return ol;
  }
  private static record CallLike(inference.E e,List<inference.E> es,Optional<RC> rc,List<IT> targs){}
  private static CallLike callLike(inference.E o,MName name){
    return switch (o){
      case inference.E.Call(var e, var n, var rc, var targs, var es, _, _, _) when n.equals(name) -> new CallLike(e,es,rc,targs);
      case inference.E.ICall(var e, var n, var es, _, _, _) when n.equals(name) -> new CallLike(e,es,Optional.empty(),List.of());
      default -> throw Bug.unreachable();
    };
  }
  private List<String> nUnderscores(int n){ return Stream.generate(()->"_").limit(n).toList(); }
  
  private static final Optional<E> synteticBody= Optional.of(new E.X("this",Src.syntetic));
  core.M mSyntetic(inference.M m){
    var s= sig(m.sig(),m.sig());
    if (m.impl().isEmpty()){ return new core.M(s,nUnderscores(s.ts().size()),Optional.empty()); }
    var i= m.impl().get();
    return new core.M(s,i.xs(),synteticBody);
  }
  public List<core.M> msSyntetic(List<inference.M> ms){ return ms.stream().map(this::mSyntetic).toList(); }
}