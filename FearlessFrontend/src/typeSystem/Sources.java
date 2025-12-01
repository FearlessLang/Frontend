package typeSystem;

import static offensiveUtils.Require.*;
import java.util.*;

import core.B;
import core.E.Literal;
import core.M;
import core.Sig;
import core.T;
import fearlessParser.RC;
import inject.TypeRename;

class Sources {
//TODO: Similar code must exists inside inference. We may or may not be able to deduplicate it (works on different types).
//But at least we can check if the two implementations are consistent and pull them to the same file so that they stay closed together.
  static List<Sig> collect(TypeSystem ts, Literal l){//Note: this uses l instead of D[Ts] since more direct/efficient
    List<Sig> sources= new ArrayList<>();
    for(T.C parent : l.cs()){
      Literal parentDef= ts.decs().apply(parent.name());
      List<Sig> parentSigs= collect(ts, parentDef);      
      List<String> parentXs= parentDef.bs().stream().map(B::x).toList();
      List<T> parentTs= parent.ts();
      for(Sig s : parentSigs){
        Sig canonical= findCanonical(l, s.m().s(), s.rc());
        sources.add(instantiate(s, parentXs, parentTs, canonical.bs()));
      }
    }
    for(M m : l.ms()){ if(m.sig().origin().equals(l.name())){ sources.add(m.sig()); } }
    return sources;
  }
  private static Sig findCanonical(Literal l, String name, RC rc){
    for(M m : l.ms()){
      var found= m.sig().m().s().equals(name) && m.sig().rc() == rc;
      if(found){ return m.sig(); }
    }
    throw new AssertionError("Method " + rc + " " + name + " not found in " + l.name().s());
  }
  private static Sig instantiate(Sig s, List<String> xs, List<T> ts, List<B> canonical){
    assert eq(s.bs().size(), canonical.size(), "Generic arity mismatch in instantiate");
    List<String> mapXs= new ArrayList<>();
    List<T> mapTs= new ArrayList<>();
    List<String> methodVars= new ArrayList<>();
    for(int i= 0; i < s.bs().size(); i++){
      String sourceVar= s.bs().get(i).x();
      String targetVar= canonical.get(i).x();
      methodVars.add(sourceVar);
      mapXs.add(sourceVar);
      mapTs.add(new T.X(targetVar));
    }
    for(int i= 0; i < xs.size(); i++){
      String var = xs.get(i);
      mapXs.add(var);
      mapTs.add(ts.get(i));
    }
    var newTs= TypeRename.ofT(s.ts(), mapXs, mapTs);
    var newRet= TypeRename.of(s.ret(), mapXs, mapTs);
    return new Sig(s.rc(), s.m(), canonical, newTs, newRet, s.origin(), s.abs(), s.pos());
  }
}