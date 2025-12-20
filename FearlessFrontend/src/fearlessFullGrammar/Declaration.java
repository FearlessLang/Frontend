package fearlessFullGrammar;

import static offensiveUtils.Require.*;
import java.util.List;
import java.util.Optional;
import utils.Pos;
public record Declaration(TName name, Optional<List<B>> bs, List<T.C> cs, E.Literal l) implements core.Src.SrcObj{
  public Declaration{
    assert nonNull(name,l);
    assert bs.isPresent() || name.arity() == 0:" name arity should be zero";
    assert validOpt(bs,b->{
      unmodifiableDistinct(b, "E.TypeDeclarationLiteral.bs");
      eq(name.arity(),b.size(),"E.TypeDeclarationLiteral.bs");
    });
    assert unmodifiable(cs,"Declaration.cs");    
  }
  public Pos pos(){ return l.pos(); }
  public TSpan span(){ return l.span(); }
}