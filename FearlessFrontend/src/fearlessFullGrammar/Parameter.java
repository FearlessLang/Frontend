package fearlessFullGrammar;

import java.util.Optional;

public record Parameter(Optional<XPat> xp, Optional<T> t){
  public Parameter{ assert xp.isPresent() || t.isPresent(); }//can be both
}