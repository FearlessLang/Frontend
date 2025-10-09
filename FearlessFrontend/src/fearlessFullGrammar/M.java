package fearlessFullGrammar;

import static offensiveUtils.Require.nonNull;

import java.util.Optional;

public record M(Optional<Sig> sig, Optional<E> body){
  public M{
    assert nonNull(sig,body);
    assert sig.isPresent() || body.isPresent();
  }
}