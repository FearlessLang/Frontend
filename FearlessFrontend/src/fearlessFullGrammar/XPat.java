package fearlessFullGrammar;

import static fearlessParser.TokenKind.CCurlyId;
import static fearlessParser.TokenKind.validate;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;
import static offensiveUtils.Require.validOpt;

import java.util.List;
import java.util.Optional;

public sealed interface XPat {
  <R> R accept(XPatVisitor<R> v);
  record Name(E.X x) implements XPat{
    public Name{ assert nonNull(x); }
    public <R> R accept(XPatVisitor<R> v){ return v.visitXPatName(this);}
  }
  //xE ::= x m* is represented as an element of extract, for example 
  //new Destruct(List.of(List.of(.foo,.bar,.baz),List.of(.x.y)),Optional.of("1"))
  //represents {foo.bar.baz,x.y}1 
  record Destruct(List<List<MName>> extract, Optional<String> id) implements XPat{
    public Destruct{
      assert unmodifiable(extract, "ParamPat.Destruct.extract",
        sm->unmodifiable(sm,"ParamPat.Destruct.extract element",
          m->{assert m.s().startsWith(".");}));
      assert validOpt(id,n -> validate("}"+n, "pattern id",CCurlyId));
    }
    public <R> R accept(XPatVisitor<R> v){ return v.visitXPatDestruct(this);}
  }
}