/*package inferenceGrammar;

import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;
import java.util.stream.Collectors;

import fearlessFullGrammar.TName;
import files.Pos;

public record Declaration(TName name, List<B> bs, List<IT.C> cs, E.Literal l){
  public Declaration{
    assert nonNull(name,l);
    assert unmodifiable(bs,"Declaration.bs");
    assert unmodifiable(cs,"Declaration.cs");
  }
  Pos pos(){ return l.pos(); }
  public String toString(){
    var bsS= bs.isEmpty()?"":"["+bs.stream().map(Object::toString).collect(Collectors.joining(", "))+"]";
    var csS= cs.stream().map(Object::toString).collect(Collectors.joining(", "));
    return name.s()+bsS+":"+csS+l;
  }
}*/