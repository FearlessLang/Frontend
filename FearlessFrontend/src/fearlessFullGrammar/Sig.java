package fearlessFullGrammar;

import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.validOpt;

import java.util.List;
import java.util.Optional;

import fearlessParser.RC;

public record Sig(
  Optional<RC> rc, Optional<MName> m,
  Optional<List<B>> bs, boolean hasParenthesis,
  List<Parameter> parameters, Optional<T> t
  ){
  public Sig{
    assert nonNull(rc,m,bs,parameters,t);
    assert validOpt(m,_m->eq(_m.arity(),parameters.size(),"Method name arity"));
  }
  public boolean fullyTyped(){
    return !(m.isEmpty() || t.isEmpty() || parameters.stream().anyMatch(p->p.t().isEmpty()));
  }
}