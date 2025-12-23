package fearlessFullGrammar;

import static offensiveUtils.Require.*;
import java.util.List;
import java.util.Optional;

import core.MName;
import core.RC;

public record Sig(
  Optional<RC> rc, Optional<MName> m,
  Optional<List<B>> bs, boolean hasParenthesis,
  List<Parameter> parameters, Optional<T> t
  ){
  public Sig{
    assert nonNull(rc,m,bs,t);
    assert unmodifiableDistinct(parameters,"Sig.parameters");
    //NO: can be +1 with implicit assert validOpt(m,_m->eq(_m.arity(),parameters.size(),"Method name arity"));
  }
  public Sig withImplicit(){
    if (m.isEmpty()){ return this; }
    return new Sig(rc,m.map(mi->mi.withArity(parameters.size()+1)),bs,hasParenthesis,parameters, t);
  }
  public boolean fullyTyped(){
    return !(m.isEmpty() || t.isEmpty() || parameters.stream().anyMatch(p->p.t().isEmpty()));
  }
}