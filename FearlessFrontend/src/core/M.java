package core;

import static offensiveUtils.Require.*;
import java.util.List;
import java.util.Optional;

import utils.Join;
public record M(Sig sig, List<String> xs, Optional<core.E> e){
  public M{
    assert nonNull(sig,e);
    assert unmodifiable(xs,"M.xs");
    assert xs.size() == sig.ts().size();
  }
  public String _toString(){
    String _xs=Join.of(xs, "(",",",")","");
    String _e=e.isEmpty()?"":"->"+e.get();
    return ""+sig+_xs+_e;
  }
  public String toString(){
    var sb= new StringBuilder();
    sb.append(sig.rc().toStrSpace());
    sb.append(sig.m());
    if (!sig.bs().isEmpty()){ sb.append(Join.of(sig.bs(),"[",",","]","")); }
    if (!xs.isEmpty()){
      sb.append('(');
      for (int i= 0; i < xs.size(); i += 1){
        if (i>0){ sb.append(", "); }
        sb.append(xs.get(i)).append(':').append(sig.ts().get(i));
      }
      sb.append(')');
    }
    sb.append(':').append(sig.ret());
    e.ifPresent(body->sb.append("->").append(body));
    return sb.toString();
  }
}