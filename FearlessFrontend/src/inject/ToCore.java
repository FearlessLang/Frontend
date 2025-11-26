package inject;

import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;

import core.B;
import core.E;
import core.T;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;
import inference.IT;
import inference.M;

public class ToCore {
//TODO: this needs to take the original exp too to merge stuff if some type was overridden
  core.E of(inference.E exp){return switch(exp){
    case inference.E.X(var name, _, Pos pos, _) -> x(name,pos);
    case inference.E.Type(var type, _, Pos pos, _) -> type(type,pos);
    case inference.E.Literal(var rc, var name, var bs, var cs, String thisName, List<M> ms, _, Pos pos, _, _) -> literal(rc.get(),name,bs,cs,thisName,ms,pos);
    case inference.E.Call(var e, var name, Optional<RC> rc, var targs, var es, _, Pos pos, _) -> call(e,name,rc.get(),targs,es,pos);
    case inference.E.ICall(var e, var name, var es, _, Pos pos, _)-> call(e,name,RC.imm,List.of(),es,pos);
  };}
  core.E.X x(String name, Pos pos){ return new core.E.X(name, pos); }
  core.E.Type type(IT.RCC type, Pos pos){
    var t= new T.RCC(type.rc(),TypeRename.itcToTC(type.c()));
    return new core.E.Type(t, pos);
  }
  core.E.Literal literal(RC rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, Pos pos){
    return new core.E.Literal(rc, name, bs,
      TypeRename.itcToTC(cs), thisName,
      ms.stream().map(m->m(m)).toList(), pos);
  }
  core.E.Call call(inference.E e, MName name, RC rc, List<IT> targs, List<inference.E> es, Pos pos){
    return new core.E.Call(of(e), name, rc,
      TypeRename.itToT(targs),
      es.stream().map(ei->of(ei)).toList(), pos);
  }
  core.M m(inference.M m){
    var s= sig(m.sig());
    if (m.impl().isEmpty()){ return new core.M(s,nUnderscores(s.ts().size()),Optional.empty()); }
    var i= m.impl().get();
    E e= of(i.e());
    return new core.M(s,i.xs(),Optional.of(e));
  }
  private static final Optional<E> synteticBody= Optional.of(new E.X("this",Pos.UNKNOWN));
  core.M mSyntetic(inference.M m){
    var s= sig(m.sig());
    if (m.impl().isEmpty()){ return new core.M(s,nUnderscores(s.ts().size()),Optional.empty()); }
    var i= m.impl().get();
    return new core.M(s,i.xs(),synteticBody);
  }
  public List<core.M> msSyntetic(List<inference.M> ms){ return ms.stream().map(this::mSyntetic).toList(); }
  core.Sig sig(inference.M.Sig s){
    //TODO: this should assert that the recreated inferenceCore.M.Sig is equals to the one in the inference computed class table
    //This will require adding a parameter to such table 
    var ts= TypeRename.itOptToT(s.ts());
    var ret= TypeRename.itToT(s.ret().get());
    return new core.Sig(s.rc().get(),s.m().get(),s.bs().get(),ts,ret,s.origin().get(),s.abs(),s.pos());
  }  
  private static List<String> _under(int n){ return IntStream.range(0, n).mapToObj(_->"_").toList(); }
  static List<List<String>> smallUnder=IntStream.range(0, 100).mapToObj(i->_under(i)).toList();
  private List<String> nUnderscores(int n){ return n < 100 ? smallUnder.get(n): _under(n); }
}