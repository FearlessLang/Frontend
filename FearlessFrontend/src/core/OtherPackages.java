package core;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import core.E.Literal;

public interface OtherPackages{
  core.E.Literal of(TName name);
  Collection<TName> dom();
  static OtherPackages empty(){ return new OtherPackages(){
    public Collection<TName> dom(){ return List.of(); }
    public core.E.Literal of(TName name){ return null; }
  };}
  default long stamp(){ return -1; }
  default Map<String,Map<String,String>> map(){ return Map.of(); }
  default OtherPackages mergeWith(List<Literal> core, long newStamp){ return this; }
}