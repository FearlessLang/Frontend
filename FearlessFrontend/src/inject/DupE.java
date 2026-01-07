package inject;

import java.util.List;
import java.util.Optional;

import core.TName;
import inference.E;
import inference.Gamma;
import inference.M;
import naming.FreshPrefix;

public record DupE(FreshPrefix fresh, E.Literal out, M m,message.WellFormednessErrors err){
  public E of(E e){ return switch (e){
    case E.X x -> new E.X(x.name(), x.t(), x.src(), new Gamma.GammaSignature());
    case E.Type t -> new E.Type(t.type(), t.t(), t.src(), new Gamma.GammaSignature());
    case E.ICall c -> new E.ICall(of(c.e()), c.name(), ofEs(c.es()), c.t(), c.src(), new Gamma.GammaSignature());
    case E.Call c -> new E.Call(of(c.e()), c.name(), c.rc(), c.targs(), ofEs(c.es()), c.t(), c.src(), new Gamma.GammaSignature());
    case E.Literal l -> ofL(l);
  };}
  private List<E> ofEs(List<E> es){ return es.stream().map(this::of).toList(); }

  private E.Literal ofL(E.Literal l){
    if (!l.infName()){ throw err.duplicatedNamedLiteral(out,m,l); }
    TName oldName= l.name();
    TName newName= fresh.freshTopType(oldName, oldName.arity());
    List<M> ms= l.ms().stream().map(m->ofM(m, oldName, newName)).toList();
    return new E.Literal(l.rc(), newName, l.bs(), l.cs(), l.thisName(), ms, l.t(), l.src(), true, l.infHead(), new Gamma.GammaSignature());
  }
  public M ofM(M m, TName oldName, TName newName){
    var sig= m.sig();
    if (sig.origin().isPresent() && sig.origin().get().equals(oldName)){ sig= sig.withOrigin(newName); }
    Optional<M.Impl> impl= m.impl().map(i->new M.Impl(i.m(), i.xs(), of(i.e())));
    return new M(sig, impl);
  }
}