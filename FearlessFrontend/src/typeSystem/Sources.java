package typeSystem;

import static offensiveUtils.Require.*;
import java.util.*;
import java.util.stream.Stream;

import core.B;
import core.E.Literal;
import core.M;
import core.Sig;
import core.T;
import fearlessParser.RC;
import inject.TypeRename;
import utils.OneOr;

class Sources {
//TODO: Similar code must exists inside inference. We may or may not be able to deduplicate it (works on different types).
//But at least we can check if the two implementations are consistent and pull them to the same file so that they stay closed together.
  static List<Sig> collect(TypeSystem ts, Literal l){//Note: this uses l instead of D[Ts] since more direct/efficient
    List<Sig> sources= new ArrayList<>();
    for(T.C parent : l.cs()){
      Literal parentDef= ts.decs().apply(parent.name());
      List<Sig> parentSigs= collect(ts, parentDef);      
      List<String> parentXs= parentDef.bs().stream().map(B::x).toList();
      for(Sig s : parentSigs){
        Sig canonical= findCanonical(l, s.m().s(), s.rc());
        sources.add(instantiate(s, parentXs, parent.ts(), canonical.bs()));
      }
    }
    for (M m : l.ms()){ if (m.sig().origin().equals(l.name())){ sources.add(m.sig()); } }
    assert unionCount(ts,l) == sources.size();
    assert sources.stream().allMatch(s->l.ms().stream().anyMatch(m->m.sig().m().equals(s.m()) && m.sig().rc() == s.rc()));
    assert l.ms().stream().map(M::sig).allMatch(s->sources.contains(s)):
      l.ms().stream().map(M::sig).toList()+" @@ "+sources;//This fails
    return sources;
  }
  private static long unionCount(TypeSystem ts, Literal l){
    return supers(ts,l).flatMap(li->
      li.ms().stream().map(M::sig).filter(s->s.origin().equals(li.name()))
    ).count();
  }
  private static Stream<Literal> supers(TypeSystem ts, Literal l){
    return Stream.concat(Stream.of(l),
      l.cs().stream().map(T.C::name).map(ts.decs()::apply)
        .flatMap(p->supers(ts,p)));
  }
  private static Sig findCanonical(Literal l, String name, RC rc){
    return OneOr.of("Methods with duplicates",l.ms().stream().map(M::sig).filter(s->
      s.m().s().equals(name) && s.rc() == rc));
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
    return new Sig(s.rc(), s.m(), canonical, newTs, newRet, s.origin(), s.abs(), s.span());
  }
}