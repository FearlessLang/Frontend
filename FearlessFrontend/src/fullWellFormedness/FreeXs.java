package fullWellFormedness;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;
import inferenceGrammar.B;
import inferenceGrammar.E;
import inferenceGrammar.E.*;
import inferenceGrammar.M;
import inferenceGrammar.IT;

public class FreeXs {
  Stream<IT.X> ftvE(E e){ return switch(e){
    case X(_, _, _,_) -> Stream.of();
    case Literal(_, var ms,_,_,_,_) -> ftvMs(ms);
    case Call(var ei, _,_, var targs, var es,_,_,_,_) -> Stream.concat(ftvE(ei),Stream.concat(ftvTs(targs),ftvEs(es)));
    case ICall(var ei,_, var es,_,_,_) -> Stream.concat(ftvE(ei),ftvEs(es));
    case Type(var type,_,_,_) -> ftvT(type);
  };}
  Stream<IT.X> ftvM(M m){
    List<String> domBs= m.sig().bs().map(bs->dom(bs)).orElse(List.of());
    return Stream.concat(
      ftvS(m.sig()),
      m.impl().stream().flatMap(this::ftvI)
    ).filter(x->!domBs.contains(x.name()));
  }
  List<String> dom(List<B> bs){ return bs.stream().map(b->b.x().name()).toList(); }
  Stream<IT.X> ftvS(M.Sig m){ return Stream.concat(ftvOTs(m.ts()),ftvT(m.ret())); }
  Stream<IT.X> ftvI(M.Impl m){ return ftvE(m.e()); }
  Stream<IT.X> ftvT(Optional<IT> o){ return o.map(t->ftvT(t)).orElse(Stream.of()); }
  Stream<IT.X> ftvT(IT t){ return switch(t){
    case IT.X x -> Stream.of(x);
    case IT.RCX(_, var x) -> Stream.of(x);
    case IT.ReadImmX(var x) -> Stream.of(x);
    case IT.RCC(_, var c) -> ftvTs(c.ts());
    case IT.U.Instance -> Stream.of();
    case IT.Err.Instance -> Stream.of();
  };}
  Stream<IT.X> ftvEs(List<E> es){ return es.stream().flatMap(this::ftvE); }
  Stream<IT.X> ftvMs(List<M> ms){ return ms.stream().flatMap(this::ftvM); }
  Stream<IT.X> ftvOTs(List<Optional<IT>> ts){ return ts.stream().flatMap(this::ftvT); }
  Stream<IT.X> ftvTs(List<IT> ts){ return ts.stream().flatMap(this::ftvT); }
}