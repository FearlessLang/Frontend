package inferenceCore;

import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;
import inference.E;
public record M(Sig sig, List<String> xs, Optional<E> e){
  public M{ assert nonNull(sig,e); assert unmodifiable(xs,"par names"); }
  public String toString(){
    var args= "";
    if (!xs.isEmpty()){ args= "("+xs.stream().collect(Collectors.joining(", "))+")"; }
    return sig + args+ (e.isPresent()? "->"+e.get()+";" : ""); 
  }
  public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, TName origin, boolean abs, Pos pos){
    public String toString(){
      var bsS= bs.isEmpty()?"":"["+bs.stream().map(Object::toString).collect(Collectors.joining(","))+"]";
      var tsS= ts.isEmpty() ? "" : "("+ts.stream().map(Object::toString).collect(Collectors.joining(","))+")";
      var rcS= rc==RC.imm?"":rc.toString()+" ";      
      var ori= "@"+origin.s();      
      var mS= m.toString();
      return " "+rcS+mS+bsS+tsS+":"+ret+ori+";";
    }
  }
}