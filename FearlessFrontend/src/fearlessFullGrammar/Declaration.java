package fearlessFullGrammar;

import static offensiveUtils.Require.eq;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;
import static offensiveUtils.Require.validOpt;

import java.util.List;
import java.util.Optional;
import files.Pos;

public record Declaration(TName name, Optional<List<B>> bs, List<T.C> cs, E.Literal l){
  public Declaration{
    assert nonNull(name,l);
    assert bs.isPresent() || name.arity() == 0:" name arity should be zero";
    assert validOpt(bs,b->{
      unmodifiable(b, "E.TypeDeclarationLiteral.bs");
      eq(name.arity(),b.size(),"E.TypeDeclarationLiteral.bs");
    });
    assert unmodifiable(cs,"Declaration.cs");    
  }
  public Pos pos(){ return l.pos(); }
}