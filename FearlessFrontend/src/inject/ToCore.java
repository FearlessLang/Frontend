package inject;

import java.util.*;
import java.util.stream.IntStream;

import core.E;
import core.T;
import fearlessFullGrammar.MName;
import fearlessParser.RC;
import files.Pos;
import inference.IT;
import utils.Bug;
import utils.OneOr;

public class ToCore{
  core.E of(inference.E exp, inference.E orig){ return switch(exp){
    case inference.E.X(var name, _, Pos pos, _) -> x(name,pos);
    case inference.E.Type(var type, _, Pos pos, _) -> type(type,pos);
    case inference.E.Literal le -> literal(le,litLike(orig,le));
    case inference.E.Call ce -> call(ce,callLike(orig,ce.name()));
    case inference.E.ICall ic -> callFromICall(ic,callLike(orig,ic.name()));
  };}
  core.E.X x(String name, Pos pos){ return new core.E.X(name,pos); }
  core.E.Type type(IT.RCC type, Pos pos){
    var t= new T.RCC(type.rc(),TypeRename.itcToTC(type.c()));
    return new core.E.Type(t,pos);
  }
  core.E.Literal literal(inference.E.Literal e, inference.E.Literal o){
    var rc= o.rc().orElse(e.rc().orElseThrow());//TODO: can it happen that the inference overrides the RC?
    var ms= mapMs(e.ms(),o.ms());
    return new core.E.Literal(rc,e.name(),e.bs(),TypeRename.itcToTC(e.cs()),e.thisName(),ms,e.pos());
  }
  core.E.Call call(inference.E.Call e, CallLike o){
    // annotation sites: rc, targs (use programmer-written ones if present in orig)
    var rc= o.rc.orElse(e.rc().orElseThrow());
    var targs= !o.targs.isEmpty() ? o.targs : e.targs();
    assert e.es().size() == o.es.size();
    var recv= of(e.e(),o.e);
    var args= IntStream.range(0,e.es().size()).mapToObj(i->of(e.es().get(i),o.es.get(i))).toList();
    return new core.E.Call(recv,e.name(),rc,TypeRename.itToT(targs),args,e.pos());
  }
  core.E.Call callFromICall(inference.E.ICall e, CallLike o){
    assert o.rc.isEmpty();
    assert o.targs.isEmpty();
    assert e.es().size() == o.es.size();
    var recv= of(e.e(),o.e);
    var args= IntStream.range(0,e.es().size()).mapToObj(i->of(e.es().get(i),o.es.get(i))).toList();
    return new core.E.Call(recv,e.name(),RC.imm,List.of(),args,e.pos());
  }
  private List<core.M> mapMs(List<inference.M> es, List<inference.M> os){
    return es.stream()
      .map(me->me.impl().isEmpty()? m(me,me) : m(me,matchM(os,me)))
      .toList();
  }
  private static inference.M matchM(List<inference.M> os, inference.M e){
    var p= e.sig().pos();
    return OneOr.of("failing to connect methods @"+p, os.stream().filter(o->o.sig().pos()==p));
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
    var ret= TypeRename.itToT(s.ret().get());
    return new core.Sig(s.rc().get(),s.m().get(),s.bs().get(),ts,ret,s.origin().get(),s.abs(),s.pos());
  }
  private static inference.E.Literal litLike(inference.E o,inference.E.Literal e){
    var ol=(inference.E.Literal)o;
    assert ol.name().equals(e.name());
    return ol;
  }
  private static record CallLike(inference.E e,List<inference.E> es,Optional<RC> rc,List<IT> targs){}
  private static CallLike callLike(inference.E o,MName name){
    return switch(o){
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
  
  private static final Optional<E> synteticBody= Optional.of(new E.X("this",Pos.UNKNOWN));
  core.M mSyntetic(inference.M m){
    var s= sig(m.sig());
    if (m.impl().isEmpty()){ return new core.M(s,nUnderscores(s.ts().size()),Optional.empty()); }
    var i= m.impl().get();
    return new core.M(s,i.xs(),synteticBody);
  }
  public List<core.M> msSyntetic(List<inference.M> ms){ return ms.stream().map(this::mSyntetic).toList(); }
}