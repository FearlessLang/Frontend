package inferenceGrammar;

import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;

import fearlessFullGrammar.TName;
import files.Pos;

public record Declaration(TName name, List<B> bs, List<T.C> cs, E.Literal l){
  public Declaration{
    assert nonNull(name,l);
    assert unmodifiable(bs,"Declaration.bs");
    assert unmodifiable(cs,"Declaration.cs");
  }
  Pos pos(){ return l.pos(); }
}