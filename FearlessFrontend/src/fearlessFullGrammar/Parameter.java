package fearlessFullGrammar;

import java.util.Optional;

import utils.Bug;

public record Parameter(Optional<XPat> xp, Optional<T> t){
  public Parameter{ assert xp.isPresent() || t.isPresent(); }//can be both
  XPat toXPat(){//but if it is both we cannot call those two methods
    if (xp.isEmpty() || t.isPresent()){ throw Bug.of(); }
    return xp.get();
  }
  T toT(){
    if (t.isEmpty() || xp.isPresent()){ throw Bug.of(); }
    return t.get();
  }
}