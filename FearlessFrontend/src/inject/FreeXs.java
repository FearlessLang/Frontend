package inject;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import core.B;
import inference.E;
import inference.IT;
import inference.M;
import inference.E.*;
import inference.Gamma;
import utils.Streams;

public record FreeXs(Gamma g){
  Stream<String> ftvE(E e){ return switch (e){
    case X(var name, var t, _, _) -> Stream.concat(t.ftv(),Stream.ofNullable(g._get(name)).flatMap(IT::ftv));
    case Literal l -> Streams.of(l.bs().stream().map(B::x),ftvCs(l.cs()),ftvMs(l.ms()));
    //Used to be l.bs().stream().map(b->b.x()); with comment //Correct since bs will contain all the ftv found anywhere in the literal
    //This is not correct because of inference order: we may have not inferred the l.bs() yet!
    case Call(var ei, _, _, var targs, var es, _, _, _) -> Streams.of(ftvE(ei),ftvTs(targs),ftvEs(es));
    case ICall(var ei, _, var es, _, _, _) -> Stream.concat(ftvE(ei),ftvEs(es));
    case Type(var t, _, _, _) -> t.ftv();
  };}
  private Stream<String> ftvM(M m){
    var domBs= B.xs(m.sig().bs().orElse(List.of()));
    return Streams.of(ftvOTs(m.sig().ts()),m.sig().ret().stream().flatMap(IT::ftv),m.impl().stream().flatMap(i->ftvE(i.e())))
      .filter(x->!domBs.contains(x));
  }
  public Stream<String> ftvCs(List<IT.C> cs){ return cs.stream().flatMap(c->ftvTs(c.ts())); }
  public Stream<String> ftvEs(List<E> es){ return es.stream().flatMap(this::ftvE); }
  public Stream<String> ftvMs(List<M> ms){ return ms.stream().flatMap(this::ftvM); }
  public Stream<String> ftvOTs(List<Optional<IT>> ts){ return ts.stream().flatMap(o->o.stream().flatMap(IT::ftv)); }
  public Stream<String> ftvTs(List<IT> ts){ return ts.stream().flatMap(IT::ftv); }
}