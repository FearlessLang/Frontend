package inferenceGrammar;

import static offensiveUtils.Require.nonNull;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;
public record M(Sig sig, Optional<Impl> impl){
  public M{ assert nonNull(sig,impl); }
  public String toString(){ return sig + impl.map(Object::toString).orElse(""); }
  public record Sig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Optional<IT>> ts, Optional<IT> ret, Optional<TName> origin, boolean abs, Pos pos){
    //TODO: add constructor taking all non optional and delagate. The refactor
    public String toString(){
      var bsS= bs.isEmpty() ? "[?]" : bs.get().isEmpty()?"":"["+bs.get().stream().map(Object::toString).collect(Collectors.joining(","))+"]";
      var tsS= ts.isEmpty() ? "" : "("+ts.stream().map(this::t).collect(Collectors.joining(","))+")";
      var rcS= rc.isPresent()?rc.get().toString():"?";
      var mS= m.isPresent()?m.get().toString():"";
      return " "+rcS+" "+mS+bsS+tsS+":"+t(ret)+";";
    }
    private String t(Optional<IT> ot){ return ot.map(Object::toString).orElse("?"); }
  }
  public record Impl(Optional<MName> m, List<String> xs, E e){
    public String toString(){
      var xsC= xs.stream().collect(Collectors.joining(", "));
      return " "+m.map(n->n.s()).orElse("")+"("+xsC+")->"+e+";";
    }
  }
}