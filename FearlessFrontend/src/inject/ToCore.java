package inject;

import java.util.*;
import java.util.stream.IntStream;

import core.E;
import core.Src;
import core.T;
import fearlessFullGrammar.MName;
import fearlessParser.RC;
import inference.IT;
import utils.Bug;
import utils.OneOr;

public class ToCore{
  core.E of(inference.E exp, inference.E orig){ return switch (exp){
    case inference.E.X(var name, _, Src src, _) -> x(name,src);
    case inference.E.Type(var type, _, Src src, _) -> type(type,src);
    case inference.E.Literal le -> literal(le,litLike(orig,le));
    case inference.E.Call ce -> call(ce,callLike(orig,ce.name()));
    case inference.E.ICall ic -> callFromICall(ic,callLike(orig,ic.name()));
  };}
  core.E.X x(String name, Src src){ return new core.E.X(name,src); }
  core.E.Type type(IT.RCC type, Src src){
    var t= new T.RCC(type.rc(),TypeRename.itcToTC(type.c()),type.span());
    return new core.E.Type(t,src);
  }
  core.E.Literal literal(inference.E.Literal e, inference.E.Literal o){
    var rc= o.rc().orElse(e.rc().orElse(RC.imm));
    var ms= mapMs(e.ms(),o.ms());
    return new core.E.Literal(rc,e.name(),e.bs(),TypeRename.itcToTC(e.cs()),e.thisName(),ms,e.src(),e.infName());
  }
  core.E.Call call(inference.E.Call e, CallLike o){
    var rc= o.rc.orElse(e.rc().orElse(RC.imm));
    var targs= !o.targs.isEmpty() ? o.targs : e.targs();
    assert e.es().size() == o.es.size();
    var recv= of(e.e(),o.e);
    var args= IntStream.range(0,e.es().size()).mapToObj(i->of(e.es().get(i),o.es.get(i))).toList();
    return new core.E.Call(recv,e.name(),rc,TypeRename.itToT(targs),args,e.src());
  }
  core.E.Call callFromICall(inference.E.ICall e, CallLike o){
    assert o.rc.isEmpty();
    assert o.targs.isEmpty();
    assert e.es().size() == o.es.size();
    if (e.name().s().contains("._do")){
      System.out.println(e);
    }
    var recv= of(e.e(),o.e);
    var args= IntStream.range(0,e.es().size()).mapToObj(i->of(e.es().get(i),o.es.get(i))).toList();
    return new core.E.Call(recv,e.name(),RC.imm,List.of(),args,e.src());
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
    var s= sig(e.sig());
    if (e.impl().isEmpty()){
      assert o.impl().isEmpty();
      return new core.M(s,nUnderscores(s.ts().size()),Optional.empty());
    }
    assert o.impl().isPresent();
    var ei= e.impl().get();
    var oi= o.impl().get();
    return new core.M(s,ei.xs(),Optional.of(of(ei.e(),oi.e())));
  }
  core.Sig sig(inference.M.Sig s){
    var ts= TypeRename.itOptToT(s.ts());
    var ret= TypeRename.itToT(s.ret());
    var rc= s.rc().orElse(RC.imm);
    var m= s.m().orElse(new MName(".inferenceFailed", ts.size()));
    var bs= s.bs().orElse(List.of());
    var origin= s.origin().orElse(TypeRename.inferUnknown.c().name());
    return new core.Sig(rc,m,bs,ts,ret,origin,s.abs(),s.span());
  }
  private static inference.E.Literal litLike(inference.E o,inference.E.Literal e){
    var ol=(inference.E.Literal)o;
    assert ol.name().s().equals(e.name().s()): ol.name() + " " + e.name();
    return ol;
  }
  private static record CallLike(inference.E e,List<inference.E> es,Optional<RC> rc,List<IT> targs){}
  private static CallLike callLike(inference.E o,MName name){
    return switch (o){
      case inference.E.Call(var e, var n, var rc, var targs, var es, _, _, _) -> {
        assert n.equals(name);
        yield new CallLike(e,es,rc,targs);
      }
      case inference.E.ICall(var e, var n, var es, _, _, _) -> {
        assert n.equals(name);
        yield new CallLike(e,es,Optional.empty(),List.of());
      }
      default -> throw Bug.unreachable();
    };
  }
  private static List<String> _under(int n){ return IntStream.range(0,n).mapToObj(_->"_").toList(); }
  static List<List<String>> smallUnder= IntStream.range(0,100).mapToObj(ToCore::_under).toList();
  private List<String> nUnderscores(int n){ return n < 100 ? smallUnder.get(n) : _under(n); }
  
  private static final Optional<E> synteticBody= Optional.of(new E.X("this",Src.syntetic));
  core.M mSyntetic(inference.M m){
    var s= sig(m.sig());
    if (m.impl().isEmpty()){ return new core.M(s,nUnderscores(s.ts().size()),Optional.empty()); }
    var i= m.impl().get();
    return new core.M(s,i.xs(),synteticBody);
  }
  public List<core.M> msSyntetic(List<inference.M> ms){ return ms.stream().map(this::mSyntetic).toList(); }
}