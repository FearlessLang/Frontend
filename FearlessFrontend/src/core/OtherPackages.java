package core;

import java.util.Collection;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import core.E.Literal;

public interface OtherPackages{
  Literal __of(TName name);//This method should only be used inside LiteralDeclatations and ToInference Function<TName,TName> f= tn->{..}
  Collection<TName> dom();
  long stamp();
  Map<String,Map<String,String>> virtualizationMap();
  static OtherPackages empty(){ return start(Map.of(),Map.<TName,Literal>of(),-1); }
  static OtherPackages start(Map<String,Map<String,String>> vMap, Map<TName,Literal> core, long newStamp){
    return new OtherPackages(){
      public Collection<TName> dom(){ return core.keySet(); }
      public Literal __of(TName name){ return core.get(name); }
      public long stamp(){ return newStamp; }
      public Map<String,Map<String,String>> virtualizationMap(){ return vMap; }
    };}
  static OtherPackages start(Map<String,Map<String,String>> vMap,Collection<Literal> core, long newStamp){
    var map= core.stream().collect(Collectors.toUnmodifiableMap(Literal::name, d->d));
    return start(vMap,map,newStamp);
  }
  default OtherPackages mergeWith(Map<TName,Literal> core, long newStamp){
    return start(this.virtualizationMap(),Stream.concat(this.dom().stream().map(this::__of),core.values().stream()).toList(),newStamp);
  }
}