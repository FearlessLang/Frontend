package core;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import core.E.Literal;

public interface OtherPackages{
  core.E.Literal of(TName name);
  Collection<TName> dom();
  long stamp();
  Map<String,Map<String,String>> virtualizationMap();
  static OtherPackages empty(){ return new OtherPackages(){
    public Collection<TName> dom(){ return List.of(); }
    public core.E.Literal of(TName name){ return null; }
    public  long stamp(){ return -1; }
    public  Map<String,Map<String,String>> virtualizationMap(){ return Map.of(); }
  };}
  static OtherPackages start(Map<String,Map<String,String>> vMap,List<Literal> core, long newStamp){
    var map= core.stream().collect(Collectors.toUnmodifiableMap (Literal::name, d->d));
    return new OtherPackages(){
      public Collection<TName> dom(){ return map.keySet(); }
      public core.E.Literal of(TName name){ return map.get(name); }
      public  long stamp(){ return newStamp; }
      public  Map<String,Map<String,String>> virtualizationMap(){ return vMap; }
    };}
  default OtherPackages mergeWith(Map<TName,Literal> core, long newStamp){
    var vMap= this.virtualizationMap();
    var map= Stream.concat(
      this.dom().stream().map(this::of),
      core.values().stream()
      ).collect(Collectors.toUnmodifiableMap(Literal::name, d->d));
    return new OtherPackages(){
      public Collection<TName> dom(){ return map.keySet(); }
      public core.E.Literal of(TName name){ return map.get(name); }
      public  long stamp(){ return newStamp; }
      public  Map<String,Map<String,String>> virtualizationMap(){ return vMap; }
    };}  
}