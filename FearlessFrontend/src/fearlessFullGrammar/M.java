package fearlessFullGrammar;

import static offensiveUtils.Require.nonNull;

import java.util.Optional;

import files.Pos;

public record M(Optional<Sig> sig, Optional<E> body, Pos pos){
  public M{
    assert nonNull(sig,body);
    assert sig.isPresent() || body.isPresent();
  }
  public String toString(){ return "M[sig="+sig+", body="+body+"]"; }
}