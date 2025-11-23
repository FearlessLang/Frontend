package inferenceCore;

import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;
import java.util.stream.Collectors;

import fearlessFullGrammar.TName;
import files.Pos;
import inference.B;

public record Declaration(TName name, List<B> bs, List<T.C> cs, String thisName, List<M> ms, Pos pos){
  public Declaration{
    assert nonNull(name,thisName,pos);
    assert unmodifiable(bs,"Declaration.bs");
    assert unmodifiable(cs,"Declaration.cs");
    assert unmodifiable(ms,"Declaration.ms");
  }
  public Declaration withMs(List<M> ms){ return new Declaration(name,bs,cs,thisName,ms,pos); }
  public String toString(){
    var bsS= bs.isEmpty()?"":"["+bs.stream().map(Object::toString).collect(Collectors.joining(", "))+"]";
    var csS= cs.stream().map(Object::toString).collect(Collectors.joining(", "));
    var msS= ms.stream().map(Object::toString).collect(Collectors.joining(""));
    return name.s()+bsS+":"+csS+"{'"+thisName+msS+"}";
  }
}