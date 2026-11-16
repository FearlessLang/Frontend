package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import core.MName;
import utils.Pos;

public sealed interface XPat{
  Stream<String> parameterNames();
  record Name(E.X x) implements XPat{
    public Name{ assert nonNull(x); }
    @Override public Stream<String> parameterNames(){ return Stream.of(x.name()); }
  }
  //xE ::= x m* is represented as an element of extract, for example
  //new Destruct(List.of(List.of(.foo,.bar,.baz),List.of(.x.y)),Optional.of("1"))
  //represents {foo.bar.baz,x.y}1
  record Destruct(List<List<MName>> extract, Optional<String> id, List<List<Pos>> at) implements XPat{
    public Destruct{
      assert !extract.isEmpty();
      assert unmodifiable(extract, "XPat.Destruct.extract",
        sm -> { assert !sm.isEmpty();
          unmodifiable(sm, "XPat.Destruct.extract element",
            m -> { assert m.s().startsWith("."); }); });
      assert validOpt(id, n -> validate("}"+n, "pattern id", CCurlyId));
      assert eq(at.stream().map(List::size).toList(), extract.stream().map(List::size).toList(), "XPat.Destruct.at");
    }
    @Override public Stream<String> parameterNames(){ return extract.stream().map(e -> e.getLast().s().substring(1)+id.orElse("")); }
    public Stream<String> invalidNames(){ return parameterNames().filter(x -> !isKind(x, LowercaseId) || isKind(x, RCap)); }
  }
}