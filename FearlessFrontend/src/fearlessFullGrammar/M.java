package fearlessFullGrammar;

import static offensiveUtils.Require.nonNull;

import java.util.Optional;

import fearlessParser.HasImplicitVisitor;
import files.Pos;

public record M(Optional<Sig> sig, Optional<E> body, boolean hasImplicit, Pos pos){
  public M(Optional<Sig> sig, Optional<E> body, Pos pos){this(sig,body,body.map(e->e.accept(new HasImplicitVisitor())).orElse(false),pos); }
  //Call to new HasImplicitVisitor() does not make parsing quadratic since HasImplicitVisitor does not enter in nested literals
  public M{
    assert nonNull(sig,body);
    assert sig.isPresent() || body.isPresent();
  }
  public String toString(){ return "M[sig="+sig+", body="+body+"]"; }
}