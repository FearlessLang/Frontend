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
    LinkedHashMap<TName, core.E.Literal> cache){
  boolean free(E.Literal d, Map<TName,E.Literal> rem){ return d.cs().stream().noneMatch(c->p.name().equals(c.name().pkgName()) && rem.containsKey(c.name())); }
  public static Methods create(Package p, OtherPackages other){
    return new Methods(p, other, new FreshPrefix(p), new LinkedHashMap<>());
  }
  List<List<E.Literal>> layer(List<E.Literal> decs){
    Map<TName, E.Literal> rem = new LinkedHashMap<>();
    for (E.Literal d : decs){ rem.put(d.name(), d); }
    List<List<E.Literal>> out= new ArrayList<>();
    while (!rem.isEmpty()){
      List<E.Literal> layer= rem.values().stream().filter(d->free(d,rem)).toList();
      if (layer.isEmpty()){ throw p.err().circularImplements(rem); }
      out.add(layer);
      for (E.Literal d : layer){ rem.remove(d.name()); }
    }
    return out;
  }
  public List<inference.E.Literal> registerTypeHeadersAndReturnRoots(List<E.Literal> iDecs){
    var acc= new ArrayList<E.Literal>();
    for (var l : layer(iDecs.stream().filter(d->!d.infName()).toList())){
      for (var d : l){
        var e= expandDeclaration(d,false);
        if (d.thisName().equals("this")){ acc.add(e); }
        cache.put(d.name(), injectDeclaration(e));
      }
    }
    return List.copyOf(acc);
  }
  record CsMs(List<IT.C> cs, List<inference.M.Sig> sigs){}
  //TODO: performance: currently fetch rewrites for the class generics
  //but we are likely to also do the rewriting for the meth generics very soon later.
  //can we merge the two steps? Something similar has been done for MSigL 
  CsMs fetch(E.Literal child,IT.C c,core.E.Literal d){ //d == from(c.name()); but from can be undefined for {..}.foo
    List<String> xs= d.bs().stream().map(b->b.x()).toList();
    return new CsMs(fetchCs(c),d.ms().stream().map(m->alphaSig(m,xs,c,child)).toList());
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
  core.E.Literal _from(TName name){ return LiteralDeclarations._from(name,cache::get,other); }
  public E.Literal expandDeclaration(E.Literal d, boolean setInfHead){
    List<CsMs> ds= d.cs().stream().map(c->fetch(d,c,from(c.name()))).toList();
    List<IT.C> allCs= Stream.concat(
      d.cs().stream(),
      ds.stream().flatMap(dsi->dsi.cs().stream())
        .distinct().sorted(Comparator.comparing(Object::toString))
      ).toList();
    var implied= ds.stream().flatMap(dsi->dsi.cs().stream()).toList();
    List<M.Sig> allSig= IntStream.range(0,ds.size()).filter(i->!implied.contains(d.cs().get(i)))
      .boxed().flatMap(i->ds.get(i).sigs().stream()).toList();
    List<M> allMs= pairWithSig(inferMNames(d.ms(),new ArrayList<>(allSig),d),new ArrayList<>(allSig),d);
    checkMagicSupertypes(d, allCs);
    return d.withCsMs(allCs,allMs,setInfHead);
  }
  //expandLiteral works on an incomplete literal with the cs list not there yet
  public E.Literal expandLiteral(E.Literal d, IT.C c){//Correct to have both expandLiteral and expandDeclaration
    var dd= _from(c.name());//null for the case {..}.foo
    List<M.Sig> allSig= dd==null ?List.of() : fetch(d,c,dd).sigs();
    List<M> allMs= pairWithSig(inferMNames(d.ms(),new ArrayList<>(allSig),d),new ArrayList<>(allSig),d);
    List<IT.C> allCs= Stream.concat(Stream.of(c), fetchCs(c).stream()).distinct().toList();
    return d.withCsMs(allCs, allMs, true);
  }
  public void checkMagicSupertypes(E.Literal d, List<IT.C> allCs){
    var widen= allCs.stream()
      .filter(c -> c.name().equals(LiteralDeclarations.widen))
      .toList();
    if (widen.size() > 1){ throw p.err().multipleWidenTo(d, widen); }
    if (allCs.stream().anyMatch(c->c.name().equals(LiteralDeclarations.baseId))){ checkBaseId(d); }
    if (allCs.stream().noneMatch(c->c.name().equals(LiteralDeclarations.sealed))){ return; }
    allCs.stream()
      .filter(c->!c.name().pkgName().equals(d.name().pkgName()))
      .forEach(c->notSealed(c.name(),d));
  }
  private void checkBaseId(E.Literal d){
    var ms= d.ms();
    var bad= ms.size() > 1 || ms.stream().anyMatch(m->!m.sig().m().map(hashOne::equals).orElse(true));
    if (bad){ throw p.err().baseIdNotOnlyHash(d); }
  }
  private static final MName hashOne= new MName("#",1);
  void notSealed(TName target, E.Literal owner){
    var d= LiteralDeclarations._from(target, _->null, other);
    if (!LiteralDeclarations.has(d.cs(),LiteralDeclarations.sealed)){ return; }
    throw p.err().extendedSealed(owner, target);
  }

  core.E.Literal injectDeclaration(E.Literal d){
    List<T.C> cs= TypeRename.itcToTC(d.cs());
    p().log().logInferenceDeclaration(d, cs);
    List<core.M> ms= new ToCore(List.of()).msSyntetic(d.ms());
    return new core.E.Literal(d.rc().get(),d.name(),d.bs(),cs,d.thisName(),ms,d.src(),d.infName());
  }
  inference.M withName(MName name,inference.M m){
    assert m.impl().isPresent() && m.sig().m().isEmpty();
    M.Sig s= m.sig();
    return new inference.M(new M.Sig(s.rc(),Optional.of(name),s.bs(), s.ts(),s.ret(),s.origin(),s.abs(),s.span()),m.impl());
  }
  List<M> inferMNames(List<M> ms, ArrayList<M.Sig> ss, E.Literal origin){
    assert ss.stream().allMatch(M.Sig::isFull);
    List<M> res= new ArrayList<>(ms.size());
    boolean changed= false;
    for (var m: ms){//for methods WITH name
      if (m.sig().m().isEmpty()){ continue; }
      var name= m.sig().m().get();
      ss.removeIf(s->s.m().get().equals(name));
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
      if (count > 1){ throw p.err().ambiguousImpl(origin,true,m,match); }
      assert match.isEmpty();
      ss.removeIf(s->s.m().get().arity()==arity?match.add(s):false);
      count= namesCount(match);
      if (count == 1){ res.add(withName(match.getFirst().m().get(),m)); continue; }
      if (count > 1){ throw p.err().ambiguousImpl(origin,false,m,match); }
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
      var groups= match.isEmpty() ? List.of(List.<M.Sig>of()) : List.copyOf(match.values());
      boolean first= true;
      for (var matches: groups){
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
    RC rc= s.rc().orElseGet(()->rcAgreement(ssAligned));
    return m.withSig(new M.Sig(rc,name,bs,ts,res,origin.name(),m.impl().isEmpty(),s.span()));
  }
  private List<B> agreementWithSize(List<M.Sig> ss, Sig s, Agreement at){
    List<List<B>> allBounds= ss.stream().map(e->e.bs().get()).distinct().toList();
    if (s.bs().isEmpty()){ return agreementBs(at,allBounds ); }
    var userBs= s.bs().get();
    var superBsList = ss.stream().map(e->e.bs().get()).toList();
    var superArities = superBsList.stream().map(List::size).distinct().toList();
    if (superArities.size() != 1){ throw p.err().methodGenericArityDisagreementBetweenSupers(at, superBsList); }
    if (superArities.getFirst() != userBs.size()){ throw p.err().methodGenericArityDisagreesWithSupers(at, userBs, superBsList.getFirst()); }
    var bounds= allBounds.stream().map(l->l.stream().map(e->e.rcs()).toList())
      .distinct().count();
    if (bounds!= 1){ throw p.err().methodBsDisagreementBetweenSupers(at, allBounds); }
    var supBs= allBounds.getFirst();
    assert supBs.size() == userBs.size();
    var supRCs= supBs.stream().map(b->b.rcs()).toList();
    var userRCs= userBs.stream().map(b->b.rcs()).toList();
    if (supRCs.equals(userRCs)){ return userBs; }
    throw p.err().methodBsDisagreesWithSupers(at, userBs,supBs);
  }      
  IT pairWithTs(Agreement at, int i, Optional<IT> t,List<M.Sig> ss){
    return t.orElseGet(()->agreement(at,ss.stream().map(e->e.ts().get(i).get()),
      p.err().argTypeDisagreement(i))); 
  }
  M pairWithSig(List<M.Sig> ss, E.Literal origin){
    assert !ss.isEmpty();
    if (ss.size() == 1){ return new M(ss.getFirst(),Optional.empty()); }
    var at= new Agreement(origin,ss.getFirst().rc(),ss.getFirst().m().get(),origin.span().inner);
    List<B> bs= agreementBs(at,ss.stream().map(e->e.bs().get()).distinct().toList());
    var ssAligned = alignMethodSigsTo(ss, bs);
    MName name= ssAligned.getFirst().m().get();
    List<Optional<IT>> ts= IntStream.range(0, name.arity()).mapToObj(i->Optional.of(pairWithTs(at,i,Optional.empty(),ssAligned))).toList();
    IT res= agreement(at,ssAligned.stream().map(e->e.ret().get()),p.err().retTypeDisagreement());
    var impl= ssAligned.stream().filter(e->!e.abs()).map(e->e.origin().get()).distinct().toList();
    var conflicts= ssAligned.stream().filter(e->!e.abs() || overridesAny(e,impl)).map(e->e.origin().get()).distinct().toList();
    if (conflicts.size() > 1){ throw p.err().ambiguousImplementationFor(conflicts,at); }
    TName originName= impl.size() == 1? impl.getFirst() : origin.name();
    RC rc= rcAgreement(ssAligned);
    M.Sig sig= new M.Sig(rc,name,bs,ts,res,originName,impl.isEmpty(),ssAligned.getFirst().span());
    return new M(sig,Optional.empty());
  }
  
  private boolean overridesAny(M.Sig s, List<TName> origins){
    return from(s.origin().get()).cs().stream().anyMatch(c->origins.contains(c.name()));
  }
  M toCompleteM(inference.M m,E.Literal origin){
    var s= m.sig();
    List<Optional<IT>> ts= s.ts().stream().map(t->Optional.of(t.orElseThrow(()->p.err().noSourceToInferFrom(origin,m)))).toList();
    IT res= s.ret().orElseThrow(()->p.err().noSourceToInferFrom(origin,m));
    return m.withSig(new M.Sig(s.rc().orElse(RC.imm),s.m().get(),s.bs().orElse(List.of()),ts,res,origin.name(),m.impl().isEmpty(),s.span()));
  }
  private <RR> RR agreement(Agreement at,Stream<RR> es, String msg){
    var res= es.distinct().toList();
    if (res.size() == 1){ return res.getFirst(); }
    throw p.err().noAgreement(at,res,msg);
  }
  //ssAligned is always grouped/bucketed by rc upstream (see pairWithSig callers), so rc is always uniform here.
  private RC rcAgreement(List<M.Sig> ssAligned){
    var rc= ssAligned.getFirst().rc().get();
    assert ssAligned.stream().allMatch(e->e.rc().get() == rc);
    return rc;
  }
  public record Agreement(E.Literal lit,Optional<RC> rc, MName mName, Span span){}
  
  List<B> agreementBs(Agreement at,List<List<B>> res){
    if (res.size() == 1){ return res.getFirst(); }
    var sizes= res.stream().map(List::size).distinct().count();
    if (sizes != 1){ throw p.err().methodGenericArityDisagreementBetweenSupers(at,res); }
    var bounds= res.stream().map(l->l.stream().map(e->e.rcs()).toList()).distinct().count();
    if (bounds== 1){ return res.getFirst(); }
    throw p.err().methodBsDisagreementBetweenSupers(at, res);
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