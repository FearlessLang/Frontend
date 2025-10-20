package fullWellFormedness;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import inferenceGrammar.B;
import inferenceGrammar.Declaration;
import inferenceGrammarB.M;
import utils.Bug;
import inferenceGrammar.T;

public record Methods(String pkgName, List<Declaration> iDecs, OtherPackages other, FreshPrefix fresh){
  void mayAdd(List<Declaration> layer, Declaration d, Map<TName, Declaration> rem){
    for (T.C c : d.cs()){
      var nope= pkgName.equals(c.name().pkgName()) && rem.containsKey(c.name());
      if (nope) { return; }
    }
    layer.add(d);
  }
  List<List<Declaration>> layer(List<Declaration> decs, String pkgName){
    Map<TName, Declaration> rem = new HashMap<>();
    for (Declaration d : decs){ rem.put(d.name(), d); }
    List<List<Declaration>> out= new ArrayList<>();
    while (!rem.isEmpty()){
      List<Declaration> layer= new ArrayList<>();
      for (Declaration d : rem.values()){ mayAdd(layer,d,rem); }
      if (layer.isEmpty()){ throw WellFormednessErrors.circularImplements(rem); }
      out.add(layer);
      for (Declaration d : layer){ rem.remove(d.name()); }
    }
    return out;
  }
  public List<inferenceGrammarB.Declaration> of(){
    var layers= layer(iDecs,pkgName);
    Map<TName, inferenceGrammarB.Declaration> cache = new HashMap<>();
    for(var l : layers){ 
      for (var d : of(l,cache)){ cache.put(d.name(), d); }
    }
    return cache.values().stream().sorted(Comparator.comparing(d->d.name().s())).toList();
  }
  List<inferenceGrammarB.Declaration> of(List<Declaration> ds, Map<TName, inferenceGrammarB.Declaration> cache){
    return ds.stream().map(d->expandDeclaration(d,cache)).toList();
  }
  record CsMs(List<T.C> cs, List<M.Sig> sigs){}
  CsMs fetch(inferenceGrammarB.Declaration d, T.C c){
    List<T.X> xs= d.bs().stream().map(b->b.x()).toList();
    var cs1= TypeRename.ofTC(d.cs(),xs,c.ts());
    var sigs= d.ms().stream().map(m->alphaSig(m,xs,c)).toList();
    return new CsMs(cs1,sigs);
  }
  private M.Sig alphaSig(M m, List<T.X> xs, T.C c){
    var s= m.sig();
    var fullXs= new ArrayList<>(xs);
    var fullTs= new ArrayList<>(c.ts());
    var newBs= new ArrayList<B>(s.bs().size());
    for(B b: s.bs()){//TODO: performance: skip lists above if bs is empty
      var x= b.x();
      if (fresh.isFreshGeneric(c.name(),x)){ newBs.add(b); continue; }
      assert !fullXs.contains(x);
      fullXs.add(x);
      var newX= new T.X(fresh.freshGeneric(c.name(),x.name()));
      fullTs.add(newX);
      newBs.add(new B(newX,b.rcs()));
    }
    List<T> newTs= TypeRename.ofT(s.ts(),fullXs,fullTs);
    T newRet= TypeRename.of(s.ret(),fullXs,fullTs);
    return new M.Sig(s.rc(),s.m(),newBs,newTs,newRet,s.origin(),s.abs(),s.pos());
  } 
  private inferenceGrammarB.Declaration from(TName name, Map<TName, inferenceGrammarB.Declaration> cache){
    if (name.pkgName().equals(pkgName)){ return cache.get(name); }
    return other.of(name);
  }
  private inferenceGrammarB.Declaration expandDeclaration(Declaration d, Map<TName, inferenceGrammarB.Declaration> cache){
    List<CsMs> ds= d.cs().stream()
      .map(c->fetch(from(c.name(),cache),c))
      .toList();
    List<T.C> allCs= Stream.concat(d.cs().stream(),ds.stream().flatMap(dsi->dsi.cs().stream()))
      .distinct().sorted(Comparator.comparing(Object::toString)).toList();
    List<M.Sig> allSig= ds.stream().flatMap(dsi->dsi.sigs().stream()).toList();
    List<M> allMs= pairWithSig(d.l().ms(),new ArrayList<>(allSig),d.name());
    return new inferenceGrammarB.Declaration(d.name(),d.bs(),allCs,d.l().thisName(),allMs,d.l().pos());
  }
  List<M> pairWithSig(List<inferenceGrammar.M> ms, ArrayList<M.Sig> ss, TName origin){
    List<M> res= new ArrayList<>();
    for(var m: ms){
      if(m.sig().m().isEmpty()){ continue; }
      var name= m.sig().m().get();
      var match= new ArrayList<M.Sig>();
      ss.removeIf(s->s.m().equals(name)?match.add(s):false);
      res.add(pairWithSig(match,m,origin));
    }
    for(var m: ms){
      if(m.sig().m().isPresent()){ continue; }
      var arity= m.sig().ts().size();
      var match= new ArrayList<M.Sig>();
      ss.removeIf(s->s.m().arity()==arity && s.abs()?match.add(s):false);
      var count= namesCount(match);
      if (count == 1){ res.add(pairWithSig(match,m,origin)); continue; }
      if (count > 1){ throw Bug.todo(); }//error ambiguos abstract impl
      ss.removeIf(s->s.m().arity()==arity?match.add(s):false);
      count= namesCount(match);
      if (count == 1){ res.add(pairWithSig(match,m,origin)); continue; }
      if (count > 1){ throw Bug.todo(); }//error ambiguos impl
      throw WellFormednessErrors.noSourceToInferFrom(m);
    }
    Map<MName,List<M.Sig>> map= ss.stream().collect(Collectors.groupingBy(s->s.m()));
    map.forEach((_,v)->res.add(pairWithSig(v,origin)));
    return List.copyOf(res);
  }
  long namesCount(List<M.Sig> ss){ return ss.stream().map(s->s.m()).count(); }
  M pairWithSig(List<M.Sig> ss, inferenceGrammar.M m, TName origin){
    if (ss.isEmpty()){ return toM(m,origin); }
    var s= m.sig();
    RC rc= s.rc().orElseGet(()->agreementRC(ss.stream().map(e->e.rc()),"reference capability disagreement"));
    MName name= ss.getFirst().m();
    List<B> bs= s.bs().orElseGet(()->agreementBs(ss.stream().map(e->e.bs()),"generic bounds disagreement"));
    List<T> ts= IntStream.range(0, s.ts().size()).mapToObj(i->pairWithTs(i, s.ts().get(i),ss)).toList();
    T res= s.ret().orElseGet(()->agreementT(ss.stream().map(e->e.ret()),"returun type disagreement"));
    boolean abs= m.impl().isEmpty();
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,origin,abs,s.pos());
    return new M(sig,m.impl());
  }
  T pairWithTs(int i, Optional<T> t,List<M.Sig> ss){
    return t.orElseGet(()->agreementT(ss.stream().map(e->e.ts().get(i)),
      "Type argument "+i+"reference capability disagreement")); 
  }
  M pairWithSig(List<M.Sig> ss, TName origin){
    assert !ss.isEmpty();
    if (ss.size() == 1){ return toM(ss.getFirst()); }
    RC rc= agreementRC(ss.stream().map(e->e.rc()),"reference capability disagreement");
    MName name= ss.getFirst().m();
    List<B> bs= agreementBs(ss.stream().map(e->e.bs()),"generic bounds disagreement");
    List<T> ts= IntStream.range(0, name.arity()).mapToObj(
      i->agreementT(ss.stream().map(e->e.ts().get(i)),
        "Type argument "+i+"reference capability disagreement")).toList();
    T res= agreementT(ss.stream().map(e->e.ret()),"returun type disagreement");
    var impl= ss.stream().filter(e->e.abs()).map(e->e.origin()).distinct().toList();
    if (impl.size() > 1){ throw Bug.todo(); }//more then one implemented
    if (impl.size() == 1){ origin = impl.getFirst(); }
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,origin,impl.isEmpty(),ss.getFirst().pos());
    return new M(sig,Optional.empty());
  }
  M toM(M.Sig s){ return new M(s,Optional.empty()); }
  M toM(inferenceGrammar.M m,TName origin){
    var s= m.sig();
    RC rc=s.rc().orElse(RC.imm);
    MName name= s.m().get();
    List<B> bs= s.bs().orElse(List.of());
    List<T> ts= s.ts().stream().map(t->t.orElseThrow(Bug::todo)).toList();
    T res= s.ret().orElseThrow(()->WellFormednessErrors.noRetNoInference(m));
    boolean abs= m.impl().isEmpty();
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,origin,abs,s.pos());
    return new M(sig,m.impl());
  }
  List<B> agreementBs(Stream<List<B>> es, String msg){
    var res= es.distinct().toList();
    if (res.size() == 1){ return res.getFirst(); }
    throw Bug.todo();//err using res and msg
  }
  T agreementT(Stream<T> es, String msg){
    var res= es.distinct().toList();
    if (res.size() == 1){ return res.getFirst(); }
    throw Bug.todo();//err using res and msg
  }
  RC agreementRC(Stream<RC> es, String msg){
    var res= es.distinct().toList();
    if (res.size() == 1){ return res.getFirst(); }
    throw Bug.todo();//err using res and msg    
  }
}
  /*
  private void collect(T.C c, Set<TName> visited, Set<T.C> out){
    if (!visited.add(c.name())){ throw WellFormednessErrors.circularImplements(c.name()); }
    if (!out.add(c)){ return; }
    for (T.C next : expandOnce(c)){
      var in= next.name().pkgName().equals(pkg.name());
      if (in){ collect(next, visited, out); }
      else{ out.add(next); out.addAll(other.impl(next)); }
    }
    visited.remove(c.name());//other branches may see n with different Ts
  }
  private List<T.C> expandImplements(List<T.C> cs){
    Set<T.C> out = new HashSet<>();
    cs.forEach(c->collect(c, new HashSet<>(), out));
    return out.stream()
      .sorted(Comparator.comparing(Object::toString))
      .toList();
  }
  private List<T.C> expandOnce(T.C c){
    if (!c.name().pkgName().equals(pkg.name())){ return other.impl(c); }
    assert c.name().pkgName().equals(pkg.name());
    var d= pkg.get(c.name());
    List<inferenceGrammar.T.C> cs= mapC(d.cs());
    if (d.bs().isEmpty()){ assert c.ts().isEmpty(); return cs; }
    List<inferenceGrammar.T.X> xs= d.bs().get().stream().map(b->visitTX(b.x())).toList();
    return TypeRename.ofTC(cs,xs,c.ts());
  }

/*List<M> sources(T.C c){
  List<M> direct= 
  List<M> inherted=
}*/
/*overrideOk(D[Ts]) holds iff ∀ mtype1 ∈ sources(D[Ts]), mtype2 ∈ sources(D[Ts]),
if name(mtype1) = name(mtype2) then mtype1 ≃ mtype2
*/

/*mtype1 ≃ mtype2
 m[∆]:RC_ T1..Tn -> T0 ≃ m[∆]:RC_ T1..Tn -> T0
*/

/*implementOk(D[Ts]) holds iff
∀ mtype1 ∈ sources(D[Ts]), mtype2 ∈ sources(D[Ts]), conflict(mtype1, mtype2) implies
∃ mtype3 ∈ sources(D[Ts]) such that mtype3 ≤ mtype1
*/

/*alternative(mtype1, mtype2) iff
RCi Di[_] = recvT(mtypei)
D1 ≠ D2
name(mtype1) = name(mtype2)
*/

/*conflict(mtype1, mtype2) iff
alternative(mtype1, mtype2)
not abs(mtype1) or not abs(mtype2)
*/

/*meth(D[Ts], m) = mtype iff
mtype ∈ sources(D[Ts])
name(mtype) = m
∀mtype′ ∈ sources(D[Ts]), if conflict(mtype, mtype′) then mtype ≤ mtype′ 
 */