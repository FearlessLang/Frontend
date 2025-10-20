package inferenceGrammarB;

import static offensiveUtils.Require.nonNull;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;
import inferenceGrammar.B;
import inferenceGrammar.T;
public record M(Sig sig, Optional<inferenceGrammar.M.Impl> impl){
  public M{ assert nonNull(sig,impl); }
  public String toString(){ return sig + impl.map(Object::toString).orElse(""); }
  public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, TName origin, boolean abs, Pos pos){
    public String toString(){
      var bsS= "["+bs.stream().map(Object::toString).collect(Collectors.joining(","))+"]";
      var tsS= ts.isEmpty() ? "" : "("+ts.stream().map(Object::toString).collect(Collectors.joining(","))+")";
      var rcS= rc.toString();
      var mS= m.toString();
      return " "+rcS+" "+mS+bsS+tsS+":"+ret+";";
    }
  }
}