package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;
import static offensiveUtils.Require.validOpt;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

public sealed interface XPat {
  <R> R accept(XPatVisitor<R> v);
  Stream<String> parameterNames();
  record Name(E.X x) implements XPat{
    public Name{ assert nonNull(x); }
    public <R> R accept(XPatVisitor<R> v){ return v.visitXPatName(this);}
    public Stream<String> parameterNames(){ return Stream.of(x.name()); }    
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
    public Stream<String> parameterNames(){ return extract.stream().map(e->e.getLast().s().substring(1) + id.orElse("")); }
  }
}