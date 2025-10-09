package fearlessFullGrammar;

import java.util.Optional;

import utils.Bug;

public record Parameter(Optional<XPat> xp, Optional<T> t){
  public Parameter{ assert xp.isPresent() || t.isPresent(); }
  XPat toXPat(){
    if(xp.isEmpty()){ throw Bug.of(); }
    if(t.isPresent()){ throw Bug.of(); }
    return xp.get();
  }
  T toT(){
    if(xp.isPresent()){ throw Bug.of(); }
    if(t.isEmpty()){ throw Bug.of(); }
    return t.get();
  }
}