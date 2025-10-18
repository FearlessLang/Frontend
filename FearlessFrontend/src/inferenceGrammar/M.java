package inferenceGrammar;

import static offensiveUtils.Require.nonNull;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessParser.RC;
import files.Pos;

public record M(Optional<Sig> sig, Optional<Impl> impl){
  public M{ assert nonNull(sig,impl); assert sig.isPresent() || impl.isPresent(); }
  public String toString(){
    return sig.map(Object::toString).orElse("")
      + impl.map(Object::toString).orElse("");
  }
  public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, Pos pos){
    public String toString(){
      var bsS= bs.isEmpty() ? "" : "["+bs.stream().map(Object::toString).collect(Collectors.joining(","))+"]";
      var tsS= ts.isEmpty() ? "" : "("+ts.stream().map(Object::toString).collect(Collectors.joining(","))+")";
      return " "+rc+" "+m+bsS+tsS+":"+ret+";";
    }
  }
  public record Impl(Optional<MName> m, List<String> xs, E e){
    public String toString(){
      var xsC= xs.stream().collect(Collectors.joining(", "));
      return " "+m.map(n->n.s()).orElse("")+"("+xsC+")->"+e+";";
    }
  }
}