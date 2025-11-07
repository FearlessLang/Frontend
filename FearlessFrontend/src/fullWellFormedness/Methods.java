package fullWellFormedness;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import inferenceGrammar.B;
import inferenceGrammar.Declaration;
import inferenceGrammar.E;
import inferenceGrammar.IT;
import inferenceGrammar.M;
import inferenceGrammar.M.Sig;
import inferenceGrammarB.T;
import message.WellFormednessErrors;
import utils.Bug;

public record Methods(
  String pkgName, List<Declaration> iDecs,
  OtherPackages other, FreshPrefix fresh,
      Map<TName, inferenceGrammarB.Declaration> cache){
  void mayAdd(List<Declaration> layer, Declaration d, Map<TName, Declaration> rem){
    for (IT.C c : d.cs()){
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
    for(var l : layers){ 
      for (var d : of(l)){ cache.put(d.name(), d); }
    }
    return cache.values().stream().sorted(Comparator.comparing(d->d.name().s())).toList();
  }
  List<inferenceGrammarB.Declaration> of(List<Declaration> ds){
    return ds.stream().map(d->injectDeclaration(expandDeclaration(d))).toList();
  }
  record CsMs(List<IT.C> cs, List<inferenceGrammar.M.Sig> sigs){}
  CsMs fetch(inferenceGrammarB.Declaration d, IT.C c){
    List<String> xs= d.bs().stream().map(b->b.x().name()).toList();
    var cs1= TypeRename.ofITC(TypeRename.tcToITC(d.cs()),xs,c.ts());
    var sigs= d.ms().stream().map(m->alphaSig(m,xs,c)).toList();
    return new CsMs(cs1,sigs);
  }
  private inferenceGrammar.M.Sig alphaSig(inferenceGrammarB.M m, List<String> xs, IT.C c){
    var s= m.sig();
    var fullXs= new ArrayList<>(xs);
    var fullTs= new ArrayList<>(c.ts());
    var newBs= new ArrayList<B>(s.bs().size());
    for(B b: s.bs()){//TODO: performance: skip lists above if bs is empty
      var x= b.x().name();
      if (fresh.isFreshGeneric(c.name(),x)){ newBs.add(b); continue; }
      assert !fullXs.contains(x);
      fullXs.add(x);
      var newX= new IT.X(fresh.freshGeneric(c.name(),x));
      fullTs.add(newX);
      newBs.add(new B(newX,b.rcs()));
    }
    List<Optional<IT>> newTs= TypeRename.ofITOpt(TypeRename.tToIT(s.ts()),fullXs,fullTs);
    IT newRet= TypeRename.of(TypeRename.tToIT(s.ret()),fullXs,fullTs);
    return new inferenceGrammar.M.Sig(
      Optional.of(s.rc()),Optional.of(s.m()),Optional.of(newBs),newTs,Optional.of(newRet),Optional.of(s.origin()),s.abs(),s.pos());
  } 
  private inferenceGrammarB.Declaration from(TName name, Map<TName, inferenceGrammarB.Declaration> cache){
    if (name.pkgName().equals(pkgName)){ return cache.get(name); }
    return other.of(name);
  }
  public Declaration expandDeclaration(Declaration d){
    List<CsMs> ds= d.cs().stream()
      .map(c->fetch(from(c.name(),cache),c))
      .toList();
    List<IT.C> allCs= Stream.concat(
      d.cs().stream(),
      ds.stream().flatMap(dsi->dsi.cs().stream()))
        .distinct().sorted(Comparator.comparing(Object::toString)).toList();
    List<M.Sig> allSig= ds.stream().flatMap(dsi->dsi.sigs().stream()).toList();
    List<M> named= inferMNames(d.l().ms(),new ArrayList<>(allSig),d.name());
    List<M> allMs= pairWithSig(named,new ArrayList<>(allSig),d.name());
    return new Declaration(d.name(),d.bs(),allCs,d.l().withMs(allMs,true));
  }
  public E.Literal expandLiteral(E.Literal l, IT.C c){
    List<M.Sig> allSig= l.ms().stream().map(m->m.sig()).toList();
    List<M> named= inferMNames(l.ms(),new ArrayList<>(allSig),c.name());
    List<M> allMs= pairWithSig(named,new ArrayList<>(allSig),c.name());
    return l.withMs(allMs,true);
  }
  private inferenceGrammarB.Declaration injectDeclaration(Declaration d){
    List<T.C> cs= TypeRename.itcToTC(d.cs());
    List<inferenceGrammarB.M> ms= TypeRename.itmToM(d.l().ms());
    return new inferenceGrammarB.Declaration(d.name(),d.bs(),cs,d.l().thisName(),ms,d.l().pos());
  } 
  inferenceGrammar.M withName(MName name,inferenceGrammar.M m){
    assert m.impl().isPresent() && m.sig().m().isEmpty();
    M.Sig s= m.sig();
    s= new M.Sig(s.rc(),Optional.of(name),s.bs(), s.ts(),s.ret(),s.origin(),s.abs(),s.pos());
    return new inferenceGrammar.M(s,m.impl());
  } 
  inferenceGrammar.M.Sig injectSig(inferenceGrammarB.M.Sig s){
    throw Bug.todo();
  }
  List<M> inferMNames(List<M> ms, ArrayList<M.Sig> ss, TName origin){
    List<M> res= new ArrayList<>();
    for (var m: ms){//for methods WITH name
      if (m.sig().m().isEmpty()){ continue; }
      var name= m.sig().m().get();
      var match= new ArrayList<M.Sig>();
      ss.removeIf(s->s.m().get().equals(name)?match.add(s):false);
      res.add(m);
    }
    for (var m: ms){//for methods WITHOUT name
      if (m.sig().m().isPresent()){ continue; }
      var arity= m.sig().ts().size();
      var match= new ArrayList<M.Sig>();
      ss.removeIf(s->s.m().get().arity()==arity && s.abs()?match.add(s):false);
      var count= namesCount(match);
      if (count == 1){ res.add(withName(match.getFirst().m().get(),m)); continue; }
      if (count > 1){ throw WellFormednessErrors.ambiguosImpl(origin,true,m,match); }
      ss.removeIf(s->s.m().get().arity()==arity?match.add(s):false);
      count= namesCount(match);
      if (count == 1){ res.add(withName(match.getFirst().m().get(),m)); continue; }
      if (count > 1){ throw WellFormednessErrors.ambiguosImpl(origin,false,m,match); }
      throw WellFormednessErrors.noSourceToInferFrom(m);
    }
    return res;
  }
  List<M> pairWithSig(List<M> ms, ArrayList<M.Sig> ss, TName origin){
    List<M> res= new ArrayList<>();
    for (var m: ms){
      var name= m.sig().m().get();
      var rc= m.sig().rc();
      var match= new LinkedHashMap<RC,List<M.Sig>>();
      ss.removeIf(s->s.m().get().equals(name) && (rc.isEmpty() || rc.equals(s.rc()))?acc(match,s):false);
      if (match.isEmpty()){ res.add(pairWithSig(List.of(),m,origin)); }
      for (var matches:match.values()){ res.add(pairWithSig(Collections.unmodifiableList(matches),m,origin)); }
    }
    ss.stream()
      .collect(Collectors.groupingBy(
        s -> new Parser.RCMName(s.rc(), s.m().get()),
        LinkedHashMap::new,
        Collectors.toList()))
      .values()
      .forEach(v -> res.add(pairWithSig(v, origin)));
    return List.copyOf(res);
  }
  private boolean acc(HashMap<RC, List<Sig>> match, Sig s){
    match.computeIfAbsent(s.rc().get(),_->new ArrayList<>()).add(s);
    return true;
  }
  long namesCount(List<M.Sig> ss){ return ss.stream().map(s->s.m()).count(); }
  M pairWithSig(List<M.Sig> ss, inferenceGrammar.M m, TName origin){
    if (ss.isEmpty()){ return toCompleteM(m,origin); }
    var s= m.sig();    
    var at= new Agreement(origin, ss.getFirst().m().get(), m.sig().pos());
    MName name= ss.getFirst().m().get();
    List<B> bs= s.bs().orElseGet(()->agreementBs(at,ss.stream().map(e->e.bs().get())));
    List<Optional<IT>> ts= IntStream.range(0, s.ts().size()).mapToObj(i->Optional.of(pairWithTs(at,i, s.ts().get(i),ss))).toList();
    IT res= s.ret().orElseGet(()->agreement(at,ss.stream().map(e->e.ret().get()),"Return type disagreement"));
    boolean abs= m.impl().isEmpty();
    RC rc= s.rc().orElseGet(()->agreement(at,ss.stream().map(e->e.rc().get()),"Reference capability disagreement"));
    M.Sig sig= new M.Sig(Optional.of(rc),Optional.of(name),Optional.of(bs),ts,Optional.of(res),Optional.of(origin),abs,s.pos());
    return new M(sig,m.impl());
  }
  IT pairWithTs(Agreement at, int i, Optional<IT> t,List<M.Sig> ss){
    return t.orElseGet(()->agreement(at,ss.stream().map(e->e.ts().get(i).get()),
      "Type disagreement about argument "+i)); 
  }
  M pairWithSig(List<M.Sig> ss, TName origin){
    assert !ss.isEmpty();
    if (ss.size() == 1){ return toCompleteM(ss.getFirst()); }
    var at= new Agreement(origin,ss.getFirst().m().get(),origin.pos());
    MName name= ss.getFirst().m().get();
    List<B> bs= agreementBs(at,ss.stream().map(e->e.bs().get()));
    List<Optional<IT>> ts= IntStream.range(0, name.arity()).mapToObj(
      i->Optional.of(agreement(at,ss.stream().map(e->e.ts().get(i).get()),
        "Type disagreement about argument "+i))).toList();
    IT res= agreement(at,ss.stream().map(e->e.ret().get()),"Return type disagreement");
    var impl= ss.stream().filter(e->!e.abs()).map(e->e.origin().get()).distinct().toList();
    if (impl.size() > 1){ throw WellFormednessErrors.ambiguousImplementationFor(ss,impl,at); }
    if (impl.size() == 1){ origin = impl.getFirst(); }
    RC rc= agreement(at,ss.stream().map(e->e.rc().get()),"Reference capability disagreement");
    M.Sig sig= new M.Sig(Optional.of(rc),Optional.of(name),Optional.of(bs),ts,Optional.of(res),Optional.of(origin),impl.isEmpty(),ss.getFirst().pos());
    return new M(sig,Optional.empty());
  }
  M toCompleteM(M.Sig s){ return new M(s,Optional.empty()); }
  M toCompleteM(inferenceGrammar.M m,TName origin){
    var s= m.sig();
    RC rc=s.rc().orElse(RC.imm);
    MName name= s.m().get();
    List<B> bs= s.bs().orElse(List.of());
    List<Optional<IT>> ts= s.ts().stream().map(t->Optional.of(t.orElseThrow(Bug::todo))).toList();
    Optional<IT> res= Optional.of(s.ret().orElseThrow(()->WellFormednessErrors.noRetNoInference(origin,m)));
    boolean abs= m.impl().isEmpty();
    M.Sig sig= new M.Sig(Optional.of(rc),Optional.of(name),Optional.of(bs),ts,res,Optional.of(origin),abs,s.pos());
    return new M(sig,m.impl());
  }
  <RR> RR agreement(Agreement at,Stream<RR> es, String msg){
    var res= es.distinct().toList();
    if (res.size() == 1){ return res.getFirst(); }
    assert !msg.equals("Reference capability disagreement"): "Triggered example where RC diagreement still happens";
    throw WellFormednessErrors.agreement(at,res,msg);
  }
  public record Agreement(TName cName, MName mName, Pos pos){}
  
  List<B> agreementBs(Agreement at,Stream<List<B>> es){
    var res= es.distinct().toList();    
    if (res.size() == 1){ return normalizeBs(at.cName,res.getFirst()); }
    var sizes= res.stream().map(List::size).distinct().count();
    if (sizes!= 1){ throw WellFormednessErrors.agreementSize(at,res); }
    var bounds= res.stream().map(l->l.stream().map(e->e.rcs()).toList()).distinct().count();
    if (bounds== 1){ return normalizeBs(at.cName, res.getFirst()); }
    throw WellFormednessErrors.agreement(at,res,"Generic bounds disagreement");
  }
  private List<B> normalizeBs(TName t, List<B> candidate){
    return candidate.stream()
      .map(e->new B(freshG(t,e.x()),e.rcs()))
      .toList();
  }
  private IT.X freshG(TName t, IT.X x){
    if (fresh.isFreshGeneric(t,x.name())){ return x; }
    return new IT.X(fresh.freshGeneric(t, x.name()));
  }
}