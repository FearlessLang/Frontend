package fearlessFullGrammar;

import static offensiveUtils.Require.nonNull;

import java.util.Optional;

import core.TSpan;
import fearlessParser.HasImplicitVisitor;

public record M(Optional<Sig> sig, Optional<E> body, boolean hasImplicit, TSpan span){
  public M(Optional<Sig> sig, Optional<E> body, TSpan span){this(sig,body,body.map(e->e.accept(new HasImplicitVisitor())).orElse(false),span); }
  //Call to new HasImplicitVisitor() does not make parsing quadratic since HasImplicitVisitor does not enter in nested literals
  public M{
    assert nonNull(sig,body);
    assert sig.isPresent() || body.isPresent();
  }
  public String toString(){ return "M[sig="+sig+", body="+body+"]"; }
}