package inject;

import java.util.List;
import java.util.Optional;

import core.TName;
import inference.E;
import inference.Gamma;
import inference.M;
import message.WellFormednessErrors;
import naming.FreshPrefix;

public record DupE(FreshPrefix fresh, E.Literal out, M m, WellFormednessErrors err){
  public E of(E e){ return switch (e){
    case E.X(var name, var t, var src, _) -> new E.X(name, t, src, new Gamma.GammaSignature());
    case E.Type(var type, var t, var src, _) -> new E.Type(type, t, src, new Gamma.GammaSignature());
    case E.ICall c -> new E.ICall(of(c.e()), c.name(), ofEs(c.es()), c.t(), c.src(), new Gamma.GammaSignature());
    case E.Call c -> new E.Call(of(c.e()), c.name(), c.rc(), c.targs(), ofEs(c.es()), c.t(), c.src(), new Gamma.GammaSignature());
    case E.Literal l -> ofL(l);
  };}
  private List<E> ofEs(List<E> es){ return es.stream().map(this::of).toList(); }

  private E.Literal ofL(E.Literal l){
    if (!l.infName()){ throw err.duplicatedNamedLiteral(out,m,l); }
    var oldName= l.name();
    var newName= fresh.freshTopType(oldName, oldName.arity());
    var ms= l.ms().stream().map(m->ofM(m, oldName, newName)).toList();
    return new E.Literal(l.rc(), newName, l.bs(), l.cs(), l.thisName(), ms, l.t(), l.src(), true, l.infHead(), new Gamma.GammaSignature());
  }
  public M ofM(M m, TName oldName, TName newName){
    var sig= m.sig();
    if (sig.origin().equals(Optional.of(oldName))){ sig= sig.withOrigin(newName); }
    var impl= m.impl().map(i->new M.Impl(i.m(), i.xs(), of(i.e())));
    return new M(sig, impl);
  }
}