package inject;

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

import core.B;
import core.LiteralDeclarations;
import core.MName;
import core.OtherPackages;
import core.RC;
import core.T;
import core.TName;
import fearlessParser.Parser;
import inference.E;
import inference.IT;
import inference.M;
import inference.M.Sig;
import metaParser.Span;
import naming.FreshPrefix;
import pkgmerge.Package;

public record Methods(
    Package p, OtherPackages other, FreshPrefix fresh,
    Map<TName, core.E.Literal> cache){
  void mayAdd(List<E.Literal> layer, E.Literal d, Map<TName,E.Literal> rem){
    for (IT.C c : d.cs()){
      var nope= p.name().equals(c.name().pkgName()) && rem.containsKey(c.name());
      if (nope) { return; }
    }
    layer.add(d);
  }
  public static Methods create(Package p, OtherPackages other) {
    return new Methods(p, other, new FreshPrefix(p), new LinkedHashMap<>());
  }
  List<List<E.Literal>> layer(List<E.Literal> decs){
    Map<TName, E.Literal> rem = new HashMap<>();
    for (E.Literal d : decs){ rem.put(d.name(), d); }
    List<List<E.Literal>> out= new ArrayList<>();
    while (!rem.isEmpty()){
      List<E.Literal> layer= new ArrayList<>();
      for (E.Literal d : rem.values()){ mayAdd(layer,d,rem); }
      if (layer.isEmpty()){ throw p.err().circularImplements(rem); }
      out.add(layer);
      for (E.Literal d : layer){ rem.remove(d.name()); }
    }
    return out;
  }
  public List<inference.E.Literal> registerTypeHeadersAndReturnRoots(List<E.Literal> iDecs){
    var acc= new ArrayList<E.Literal>();
    var layers= layer(iDecs.stream().filter(d->!d.infName()).toList()); //var layers= layer(iDecs);
    for (var l : layers){ 
      for (var d : ofLayer(l,acc)){
        if(!d.infName()){ cache.put(d.name(), d); }
      }
    }
    return acc;
  }
  private List<core.E.Literal> ofLayer(List<E.Literal> ds, ArrayList<E.Literal> acc){
    return ds.stream().map(d->{
      var e= expandDeclaration(d,false);
      if (d.thisName().equals("this")){ acc.add(e); }
      return injectDeclaration(e);
    }).toList();
  }
  record CsMs(List<IT.C> cs, List<inference.M.Sig> sigs){}
  //TODO: performance: currently fetch rewrites for the class generics
  //but we are likely to also do the rewriting for the meth generics very soon later.
  //can we merge the two steps? Something similar has been done for MSigL 
  CsMs fetch(E.Literal child,IT.C c){ return fetch(child,c,from(c.name())); }
  CsMs fetch(E.Literal child,IT.C c,core.E.Literal d){ //d == from(c.name()); but from can be undefined for {..}.foo
    List<String> xs= d.bs().stream().map(b->b.x()).toList();
    var cs1= TypeRename.ofITC(TypeRename.tcToITC(d.cs()),xs,c.ts());
    List<inference.M.Sig> sigs= d.ms().stream().<inference.M.Sig>map(m->alphaSig(m,xs,c,child)).toList();
    return new CsMs(cs1,sigs);
  }
  List<IT.C> fetchCs(IT.C c){
    core.E.Literal d= _from(c.name());
    if (d == null){ return List.of(); }//case {..}.foo
    List<String> xs= d.bs().stream().map(b->b.x()).toList();
    return TypeRename.ofITC(TypeRename.tcToITC(d.cs()),xs,c.ts());
  }
  private inference.M.Sig alphaSig(core.M m, List<String> xs, IT.C c, E.Literal child){
    var s= m.sig();
    var fullXs= new ArrayList<>(xs);
    var fullTs= new ArrayList<>(c.ts());
    List<B> newBs= s.bs().isEmpty()?List.of():new ArrayList<B>(s.bs().size());
    for (B b: s.bs()){
      var x= b.x();
      if (fresh.isFreshGeneric(child.name(),x)){ newBs.add(b); continue; }
      assert !fullXs.contains(x);
      fullXs.add(x);
      var newX= new IT.X(fresh.freshGeneric(child.name(),x),child.name().approxSpan());
      fullTs.add(newX);
      newBs.add(new B(newX.name(),b.rcs()));
    }
    List<Optional<IT>> newTs= TypeRename.ofITOpt(TypeRename.tToIT(s.ts()),fullXs,fullTs);
    IT newRet= TypeRename.of(TypeRename.tToIT(s.ret()),fullXs,fullTs);
    return new inference.M.Sig(s.rc(),s.m(),Collections.unmodifiableList(newBs),newTs,newRet,s.origin(),s.abs(),child.span());
  }
  public core.E.Literal from(TName name){
    var res= _from(name);
    assert res != null: "In pkgName="+p.name()+", name not found: "+name+" current domain is:\n"+cache.keySet();
    return res;
  }
  core.E.Literal _from(TName name){ return LiteralDeclarations._from(name,cache,other); }
  public E.Literal expandDeclaration(E.Literal d, boolean setInfHead){
    List<CsMs> ds= d.cs().stream().map(c->fetch(d,c)).toList();
    List<IT.C> allCs= Stream.concat(
      d.cs().stream(),
      ds.stream().flatMap(dsi->dsi.cs().stream())
        .distinct().sorted(Comparator.comparing(Object::toString))
      ).toList();
    List<M.Sig> allSig= ds.stream().flatMap(dsi->dsi.sigs().stream()).toList();
    List<M> named= inferMNames(d.ms(),new ArrayList<>(allSig),d);
    List<M> allMs= pairWithSig(named,new ArrayList<>(allSig),d);
    checkMagicSupertypes(d, allCs);
    return d.withCsMs(allCs,allMs,setInfHead);
  }
  //expandLiteral works on an incomplete literal with the cs list not there yet
  public E.Literal expandLiteral(E.Literal d, IT.C c){//Correct to have both expandLiteral and expandDeclaration
    fresh.registerAnonSuperT(d.name(),c.name());
    var dd= _from(c.name());//null for the case {..}.foo
    List<M.Sig> allSig= dd==null ?List.of() : fetch(d,c,dd).sigs();
    List<M> named= inferMNames(d.ms(),new ArrayList<>(allSig),d);
    List<M> allMs= pairWithSig(named,new ArrayList<>(allSig),d);
    List<IT.C> allCs= Stream.concat(Stream.of(c), fetchCs(c).stream()).distinct().toList();
    return d.withCsMs(allCs, allMs, true);
  }
  public void checkMagicSupertypes(E.Literal d, List<IT.C> allCs){
    var widen= allCs.stream()
      .filter(c -> c.name().s().equals("base.WidenTo"))
      .toList();
    if (widen.size() > 1){ throw p.err().multipleWidenTo(d, widen); }
    var hasSealed= allCs.stream()
      .filter(c -> c.name().s().equals("base.Sealed"))
      .count() != 0;
    if (!hasSealed){ return; }
    if (d.ms().isEmpty()){ return; }
    allCs.stream()
      .filter(c->!c.name().pkgName().equals(d.name().pkgName()))
      .forEach(c->notSealed(c.name(),d));
  }
  void notSealed(TName target, E.Literal owner){
    boolean hasSealed= other.of(target).cs().stream()
    .filter(c -> c.name().s().equals("base.Sealed")).count() != 0;
    if (!hasSealed){ return; }
    throw p.err().extendedSealed(owner,fresh, target);
  }

  core.E.Literal injectDeclaration(E.Literal d){
    List<T.C> cs= TypeRename.itcToTC(d.cs());
    p().log().logInferenceDeclaration(d, cs);
    List<core.M> ms= new ToCore().msSyntetic(d.ms());
    return new core.E.Literal(d.rc().get(),d.name(),d.bs(),cs,d.thisName(),ms,d.src(),d.infName());
  }
  inference.M withName(MName name,inference.M m){
    assert m.impl().isPresent() && m.sig().m().isEmpty();
    M.Sig s= m.sig();
    s= new M.Sig(s.rc(),Optional.of(name),s.bs(), s.ts(),s.ret(),s.origin(),s.abs(),s.span());
    return new inference.M(s,m.impl());
  }
  List<M> inferMNames(List<M> ms, ArrayList<M.Sig> ss, E.Literal origin){
    assert ss.stream().allMatch(M.Sig::isFull);
    List<M> res= new ArrayList<>(ms.size());
    boolean changed= false;
    for (var m: ms){//for methods WITH name
      if (m.sig().m().isEmpty()){ continue; }
      var name= m.sig().m().get();
      var match= new ArrayList<M.Sig>();
      ss.removeIf(s->s.m().get().equals(name)?match.add(s):false);
      res.add(m);
    }
    for (var m: ms){//for methods WITHOUT name
      if (m.sig().m().isPresent()){ continue; }
      changed = true;
      var arity= m.sig().ts().size();
      var match= new ArrayList<M.Sig>();
      ss.removeIf(s->s.m().get().arity()==arity && s.abs()?match.add(s):false);
      var count= namesCount(match);
      if (count == 1){ res.add(withName(match.getFirst().m().get(),m)); continue; }
      if (count > 1){ throw p.err().ambiguousImpl(origin,fresh,true,m,match); }
      assert match.isEmpty();
      ss.removeIf(s->s.m().get().arity()==arity?match.add(s):false);
      count= namesCount(match);
      if (count == 1){ res.add(withName(match.getFirst().m().get(),m)); continue; }
      if (count > 1){ throw p.err().ambiguousImpl(origin,fresh,false,m,match); }
      throw p.err().noSourceToInferFrom(origin,m);
    }
    return changed ? List.copyOf(res) : ms;
  }
  List<M> pairWithSig(List<M> ms, ArrayList<M.Sig> ss, E.Literal origin){
    List<M> res= new ArrayList<>();
    boolean changed= false;
    for (var m: ms){ 
      var name= m.sig().m().get();
      var rc= m.sig().rc();
      var match= new LinkedHashMap<RC,List<M.Sig>>();    
      ss.removeIf(s->s.m().get().equals(name) && (rc.isEmpty() || rc.equals(s.rc()))?acc(match,s):false);
      if (m.sig().rc().isEmpty()  && match.size() > 1){
        var litRc= origin.rc().or(origin.t()::explicitRC).orElseThrow();
        if (litRc == RC.imm || litRc == RC.read){
          var dead= match.remove(RC.mut);
          if (dead != null){ ss.addAll(dead); }
        }
      }
      if (match.isEmpty()){
        var m2= pairWithSig(List.of(),m,origin);
        assert (m2 == m) == m2.equals(m);
        changed |= m2 != m;
        res.add(m2);
        continue;
      }
      boolean first= true;
      for (var matches: match.values()){
        var mi= first ? m : new DupE(fresh,origin,m,this.p().err()).ofM(m,origin.name(),origin.name());
        first= false;
        var m2= pairWithSig(Collections.unmodifiableList(matches), mi, origin);
        assert (m2 == mi) == m2.equals(mi);
        changed |= m2 != mi;
        res.add(m2);
      }
      //--------
    }
    if (!ss.isEmpty()){
      changed= true;
      ss.stream()
        .collect(Collectors.groupingBy(
          s -> new Parser.RCMName(s.rc(), s.m().get()),
          LinkedHashMap::new,
          Collectors.toList()))
        .values()
        .forEach(v -> res.add(pairWithSig(v, origin)));
    }
    assert !changed == res.equals(ms): changed;
    return changed ? List.copyOf(res) : ms;
  } 
  private boolean acc(HashMap<RC, List<Sig>> match, Sig s){
    match.computeIfAbsent(s.rc().get(),_->new ArrayList<>()).add(s);
    return true;
  }
  long namesCount(List<M.Sig> ss){ return ss.stream().map(s->s.m().get()).distinct().count(); }
    
  M pairWithSig(List<M.Sig> ss, inference.M m, E.Literal origin){
    if (ss.isEmpty()){ return toCompleteM(m,origin); }
    var s= m.sig();
    var at= new Agreement(origin, ss.getFirst().rc(), ss.getFirst().m().get(), m.sig().span().inner);
    List<B> bs= agreementWithSize(ss, s, at);
    var ssAligned= alignMethodSigsTo(ss, bs);
    MName name= ssAligned.getFirst().m().get();
    List<Optional<IT>> ts= IntStream.range(0, s.ts().size()).mapToObj(i->Optional.of(pairWithTs(at,i, s.ts().get(i),ssAligned))).toList();
    IT res= s.ret().orElseGet(()->agreement(at,ssAligned.stream().map(e->e.ret().get()),
      p.err().retTypeDisagreement()));
    boolean abs= m.impl().isEmpty();
    RC rc= s.rc().orElseGet(()->agreement(at,ssAligned.stream().map(e->e.rc().get()),
      p.err().refCapDisagreement()));
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,origin.name(),abs,s.span());
    if (sig.equals(m.sig())){ return m; }
    return new M(sig,m.impl());
  }
  private List<B> agreementWithSize(List<M.Sig> ss, Sig s, Agreement at){
    List<List<B>> allBounds= ss.stream().map(e->e.bs().get()).distinct().toList();
    if (s.bs().isEmpty()){ return agreementBs(at,allBounds ); }
    var userBs= s.bs().get();
    int userArity= userBs.size();
    var superBsList = ss.stream().map(e->e.bs().get()).toList();
    var superArities = superBsList.stream().map(List::size).distinct().toList();
    if (superArities.size() != 1){ throw p.err().methodGenericArityDisagreementBetweenSupers(at,fresh, superBsList); }
    var superArity= superArities.getFirst();
    if (superArity != userArity){ throw p.err().methodGenericArityDisagreesWithSupers(at,fresh,
      userArity, superArities.getFirst(), userBs, superBsList.getFirst()); }
    var bounds= allBounds.stream().map(l->l.stream().map(e->e.rcs()).toList())
      .distinct().count();
    if (bounds!= 1){ throw p.err().methodBsDisagreementBetweenSupers(at, fresh,allBounds); }
    var supBs= allBounds.getFirst();
    assert supBs.size() == userBs.size();
    var supRCs= supBs.stream().map(b->b.rcs()).toList();
    var userRCs= userBs.stream().map(b->b.rcs()).toList();
    if (supRCs.equals(userRCs)){ return userBs; }
    throw p.err().methodBsDisagreesWithSupers(at, fresh,userBs,supBs);
  }      
  IT pairWithTs(Agreement at, int i, Optional<IT> t,List<M.Sig> ss){
    return t.orElseGet(()->agreement(at,ss.stream().map(e->e.ts().get(i).get()),
      p.err().argTypeDisagreement(i))); 
  }
  M pairWithSig(List<M.Sig> ss, E.Literal origin){
    assert !ss.isEmpty();
    if (ss.size() == 1){ return toCompleteM(ss.getFirst()); }
    var at= new Agreement(origin,ss.getFirst().rc(),ss.getFirst().m().get(),origin.span().inner);
    List<B> bs= agreementBs(at,ss.stream().map(e->e.bs().get()).distinct().toList());
    var ssAligned = alignMethodSigsTo(ss, bs);
    MName name= ssAligned.getFirst().m().get();
    List<Optional<IT>> ts= IntStream.range(0, name.arity()).mapToObj(
      i->Optional.of(agreement(at,ssAligned.stream().map(e->e.ts().get(i).get()),
        p.err().argTypeDisagreement(i)))).toList();
    IT res= agreement(at,ssAligned.stream().map(e->e.ret().get()),p.err().retTypeDisagreement());
    var impl= ssAligned.stream().filter(e->!e.abs()).map(e->e.origin().get()).distinct().toList();
    if (impl.size() > 1){ throw p.err().ambiguousImplementationFor(ssAligned,impl,at,fresh); }
    TName originName= impl.size() == 1? impl.getFirst() : origin.name();
    RC rc= agreement(at,ssAligned.stream().map(e->e.rc().get()),p.err().refCapDisagreement());
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,originName,impl.isEmpty(),ssAligned.getFirst().span());
    return new M(sig,Optional.empty());
  }
  
  M toCompleteM(M.Sig s){ return new M(s,Optional.empty()); }
  M toCompleteM(inference.M m,E.Literal origin){
    var s= m.sig();
    RC rc=s.rc().orElse(RC.imm);
    MName name= s.m().get();
    List<B> bs= s.bs().orElse(List.of());
    List<Optional<IT>> ts= s.ts().stream().map(t->Optional.of(t.orElseThrow(()->p.err().noSourceToInferFrom(origin,m)))).toList();
    IT res= s.ret().orElseThrow(()->p.err().noSourceToInferFrom(origin,m));
    boolean abs= m.impl().isEmpty();
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,origin.name(),abs,s.span());
    if (sig.equals(m.sig())){ return m; }
    return new M(sig,m.impl());
  }
  private <RR> RR agreement(Agreement at,Stream<RR> es, String msg){
    var res= es.distinct().toList();
    if (res.size() == 1){ return res.getFirst(); }
    assert !msg.equals("Reference capability disagreement"): "Triggered example where RC diagreement still happens";
    throw p.err().noAgreement(at,fresh,res,msg);
    //TODO: if we can not fail the assertion below, delete stuff mentioning "Reference capability disagreement"
  }
  public record Agreement(E.Literal lit,Optional<RC> rc, MName mName, Span span){}
  
  List<B> agreementBs(Agreement at,List<List<B>> res){
    if (res.size() == 1){ return res.getFirst(); }
    var sizes= res.stream().map(List::size).distinct().count();
    if (sizes != 1){ throw p.err().methodGenericArityDisagreementBetweenSupers(at,fresh,res); }
    var bounds= res.stream().map(l->l.stream().map(e->e.rcs()).toList()).distinct().count();
    if (bounds== 1){ return res.getFirst(); }
    throw p.err().methodBsDisagreementBetweenSupers(at, fresh,res);
  }
  private List<M.Sig> alignMethodSigsTo(List<M.Sig> ss, List<B> bs){ return ss.stream().map(s->alignMethodSigTo(s,bs)).toList(); }
  private M.Sig alignMethodSigTo(M.Sig superSig, List<B> targetBs){
    assert superSig.isFull();
    if (superSig.bs().get().isEmpty()){ return superSig; }
    var fromXs = superSig.bs().get().stream().map(B::x).toList();
    var toITs  = targetBs.stream().<IT>map(b -> new IT.X(b.x(),superSig.span())).toList();
    assert fromXs.size() == toITs.size() : "mismatched method generic arity";
    var renamedTs  = TypeRename.ofOptITOpt(superSig.ts(), fromXs, toITs);
    var renamedRet = superSig.ret().map(it -> TypeRename.of(it, fromXs, toITs));
    return new M.Sig(superSig.rc(), superSig.m(), Optional.of(targetBs),
      renamedTs, renamedRet, superSig.origin(), superSig.abs(), superSig.span());
  }
}