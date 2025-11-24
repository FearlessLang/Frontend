package fearlessFullGrammar;

import static offensiveUtils.Require.*;
import java.util.List;
import java.util.Optional;
import fearlessParser.RC;

public record Sig(
  Optional<RC> rc, Optional<MName> m,
  Optional<List<B>> bs, boolean hasParenthesis,
  List<Parameter> parameters, Optional<T> t
  ){
  public Sig{
    assert nonNull(rc,m,bs,t);
    assert unmodifiable(parameters,"Sig.parameters");
    assert validOpt(m,_m->eq(_m.arity(),parameters.size(),"Method name arity"));
  }
  public boolean fullyTyped(){
    return !(m.isEmpty() || t.isEmpty() || parameters.stream().anyMatch(p->p.t().isEmpty()));
  }
}