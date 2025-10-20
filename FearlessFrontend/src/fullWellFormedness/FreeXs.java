package fullWellFormedness;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;
import inferenceGrammar.B;
import inferenceGrammar.E;
import inferenceGrammar.E.*;
import inferenceGrammar.M;
import inferenceGrammar.T;
import inferenceGrammar.IT;

public class FreeXs {
  Stream<T.X> ftvE(E e){ return switch(e){
    case X(_, _, _) -> Stream.of();
    case Literal(_, var ms,_,_) -> ftvMs(ms);
    case Call(var ei, _,_, var targs, var es,_,_) -> Stream.concat(ftvE(ei),Stream.concat(ftvITs(targs),ftvEs(es)));
    case ICall(var ei,_, var es,_,_) -> Stream.concat(ftvE(ei),ftvEs(es));
    case Type(var type,_,_) -> ftvT(type);
  };}
  Stream<T.X> ftvM(M m){
    List<T.X> domBs= m.sig().bs().map(bs->dom(bs)).orElse(List.of());
    return Stream.concat(
      ftvS(m.sig()),
      m.impl().stream().flatMap(this::ftvI)
    ).filter(x->!domBs.contains(x));
  }
  List<T.X> dom(List<B> bs){ return bs.stream().map(B::x).toList(); }
  Stream<T.X> ftvS(M.Sig m){ return Stream.concat(ftvOTs(m.ts()),ftvT(m.ret())); }
  Stream<T.X> ftvI(M.Impl m){ return ftvE(m.e()); }
  Stream<T.X> ftvT(Optional<T> o){ return o.map(t->ftvT(t)).orElse(Stream.of()); }
  Stream<T.X> ftvT(T t){ return switch(t){
    case T.X x -> Stream.of(x);
    case T.RCX(_, var x) -> Stream.of(x);
    case T.ReadImmX(var x) -> Stream.of(x);
    case T.RCC(_, var c) -> ftvTs(c.ts());
  };}
  Stream<T.X> ftvIT(IT t){ return switch(t){
    case IT.X x -> Stream.of(new T.X(x.name()));
    case IT.RCX(_, var x) -> ftvIT(x);
    case IT.ReadImmX(var x) -> ftvIT(x);
    case IT.RCC(_, var c) -> ftvITs(c.ts());
    case IT.U.Instance -> Stream.of();
  };} 
  Stream<T.X> ftvEs(List<E> es){ return es.stream().flatMap(this::ftvE); }
  Stream<T.X> ftvMs(List<M> ms){ return ms.stream().flatMap(this::ftvM); }
  Stream<T.X> ftvOTs(List<Optional<T>> ts){ return ts.stream().flatMap(this::ftvT); }
  Stream<T.X> ftvTs(List<T> ts){ return ts.stream().flatMap(this::ftvT); }
  Stream<T.X> ftvITs(List<IT> ts){ return ts.stream().flatMap(this::ftvIT); }
}