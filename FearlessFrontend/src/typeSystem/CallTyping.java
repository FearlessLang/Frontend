package typeSystem;

import java.util.List;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.stream.IntStream;
import core.*;
import core.E.*;
import inject.TypeRename;
import message.Reason;
import utils.OneOr;
import utils.Push;
import utils.Range;
import typeSystem.TypeSystem.*;

record CallTyping(TypeSystem ts, List<B> bs, Gamma g, Call c, List<TRequirement> rs){
  List<Reason> run(){
    var rcc0= recvRcc();
    var d= ts.decs().apply(rcc0.c().name());
    var sig= sigOf(d);
    checkTargsKinding(rcc0.c(),d,sig);
    var base= baseMType(rcc0.c(),d,sig);
    c.expectedRes().inner= base.t();
    var promos= MultiMeth.of(bs,base,true);
    var app= promos.stream().filter(m->rcc0.rc().isSubType(m.rc())).toList();
    if (app.isEmpty()){ throw ts.tsE().receiverRCBlocksCall(d,c,rcc0.rc(),MultiMeth.of(bs,base,mayBeH(rcc0.rc(),base))); }
    var mat= typeArgsOnce(d,app);
    var possible= mat.candidatesOkForAllArgs();//This is indexes of MTypes allowed by the arguments
    if (rs.isEmpty() && possible.isEmpty()){ throw noCandidate(d,mat); }
    if (rs.isEmpty()){ return List.of(Reason.pass(bestUnique(mat,possible))); }
    return rs.stream().map(req->resForReq(d,sig,base,rcc0.rc(),mat,possible,req)).toList();
  }
  private FearlessException noCandidate(Literal d, ArgMatrix mat){
    var argi= IntStream.range(0,mat.okByArg().size()).filter(i->mat.okByArg().get(i).isEmpty()).findFirst();
    if (argi.isEmpty()){ return ts.tsE().methodPromotionsDisagreeOnArguments(c,mat); }
    var i= argi.getAsInt();
    var cts= new TypeSystem(ts.scope().pushCallArgi(this.c, i),ts.v());
    return cts.tsE().methodArgumentCannotMeetAnyPromotion(cts,bs,d,c,i,argRequirements(mat.cs(),i),mat.resByArg().get(i));
  }
  private boolean splitOk(List<B> bs0, MType base, RC recv, ArgMatrix mat, T req){
    var ts0= Push.of(Push.of(base.ts(),base.t()),req);
    var x= bs0.stream().filter(b->b.rcs().size() > 1 && ts0.stream().anyMatch(t->mentions(t,b.x()))).findFirst();
    return x.isPresent() && x.get().rcs().stream().allMatch(rc->fits(narrow(bs0,x.get(),rc),base,recv,mat,req));
  }
  private boolean fits(List<B> bs0, MType base, RC recv, ArgMatrix mat, T req){
    var fit= MultiMeth.of(bs0,base,true).stream()
      .anyMatch(m->recv.isSubType(m.rc()) && argsFit(bs0,mat,m) && ts.isSub(bs0,m.t(),req));
    return fit || splitOk(bs0,base,recv,mat,req);
  }
  private boolean argsFit(List<B> bs0, ArgMatrix mat, MType m){
    return IntStream.range(0,m.ts().size())
      .allMatch(i->mat.resByArg().get(i).stream().anyMatch(r->ts.isSub(bs0,r.best,m.ts().get(i))));
  }
  private static List<B> narrow(List<B> bs0, B x, RC rc){
    return bs0.stream().map(b->b == x ? new B(b.x(),EnumSet.of(rc)) : b).toList();
  }
  private static boolean mentions(T t, String x){ return switch (t){
    case T.RCC(_, var c0, _) -> c0.ts().stream().anyMatch(ti->mentions(ti,x));
    case T.X _, T.RCX _, T.ReadImmX _ -> TypeSystem.xName(t).orElseThrow().equals(x);
  };}
  private boolean mayBeH(RC recv, MType base){
    return recv.isH() || Push.of(base.ts(),base.t()).stream().anyMatch(this::mayBeH);
  }
  private boolean mayBeH(T t){
    if (t instanceof T.X(var name, _)){ return RC.get(bs,name).rcs().stream().anyMatch(RC::isH); }
    return t.explicitH();
  }
  private T.RCC recvRcc(){
    var cts= new TypeSystem(ts.scope().pushCallRec(this.c),ts.v());
    var r= OneOr.of("One reason without requirements",cts.typeOf(bs,g,c.e(),List.of()).stream());
    assert r.isEmpty();//else would have thrown
    var t= r.best;
    if (t instanceof T.RCC x){ return x; }
    throw ts.tsE().methodReceiverIsTypeParameter(cts.scope(),c,t);
  }
  private Sig sigOf(Literal d){
    var sig= OneOr.opt("Methods with duplicates",d.ms().stream().map(M::sig)
      .filter(s->s.m().equals(c.name()) && s.rc() == c.rc()))
      .orElseThrow(()->ts.tsE().methodNotDeclared(ts.scope(),c,d));
    assert sig.ts().size() == c.es().size();//ensured by well formedness
    if (sig.bs().size() == c.targs().size()){ return sig; }
    throw ts.tsE().methodTArgsArityError(d,c,sig.bs());
  }
  private MType baseMType(T.C c0, Literal d, Sig sig){
    var xs= B.xs(Push.of(d.bs(),sig.bs()));
    var ts0= Push.of(c0.ts(),c.targs());
    var ps= TypeRename.ofT(sig.ts(),xs,ts0);
    var ret= TypeRename.of(sig.ret(),xs,ts0);
    return new MType("As declared",sig.rc(),ps,ret);
  }
  private void checkTargsKinding(T.C c0, Literal d, Sig sig){
    assert c0.ts().size() == d.bs().size();
    var targs= c.targs();
    var kt= new KindingTarget.CallKinding(c0,c);
    for (int i : Range.of(targs)){
      ts.k().check(c,kt,i,bs,targs.get(i),sig.bs().get(i).rcs());
    }
  }
  private ArgMatrix typeArgsOnce(Literal d,List<MType> app){
    var size= c.es().size();
    var acc= new ArgMatrix(app,new ArrayList<>(size),new ArrayList<>(size));
    for (int argi : Range.of(0,size)){
      try{ accArgi(acc,argi); }
      catch(FearlessException fe){
        if (acc.okByArg().stream().noneMatch(List::isEmpty)){ throw fe; }
        throw noCandidate(d,acc);
      }
    }
    return acc;
  }
  private List<TRequirement> argRequirements(List<MType> app, int argi){
    //TODO:This is actually a really confusing point:
    //app has MTypes pre merged if two promotions had the same MType, but their argi may
    //still be the same, so we are doing some duplicated computation when eventually do
    //the subtyping checks. The commented code below saves that duplicated computation
    //But if we deduplicate here we have to re expand directly later to be able to fit the
    //ArgMatrix acc with the right number of elements.
    return app.stream().map(m->new TRequirement(m.promotion(),m.ts().get(argi))).toList();
    /*var byT= new LinkedHashMap<T,List<String>>();
    for (var m:app){
      var t= m.ts().get(argi);
      byT.computeIfAbsent(t,_->new ArrayList<>()).add(m.promotion());
    }
    return byT.entrySet().stream()
      .map(e->new TRequirement(
        Join.of(e.getValue().stream().distinct(),"",", ",""),
        e.getKey()))
      .toList();*/
  }
  private void accArgi(ArgMatrix acc, int argi){
    var reqs= argRequirements(acc.cs(),argi);
    var cts= new TypeSystem(ts.scope().pushCallArgi(this.c, argi),ts.v());
    var res= cts.typeOf(bs,g,c.es().get(argi),reqs);
    assert res.size() == acc.cs().size();
    acc.okByArg().add(okSet(res));
    acc.resByArg().add(res);
  }
  private static List<Integer> okSet(List<Reason> res){
    return IntStream.range(0,res.size()).filter(i->res.get(i).isEmpty()).boxed().toList();
  }
  private Reason resForReq(Literal d, Sig sig, MType base, RC recv, ArgMatrix mat, List<Integer> possible, TRequirement req){
    var okRet= possible.stream()
      .filter(i->ts.isSub(bs,mat.candidate(i).t(),req.t())).toList();
    if (!okRet.isEmpty()){ return Reason.pass(bestUnique(mat,okRet)); }
    if (splitOk(bs,base,recv,mat,req.t())){ return Reason.pass(req.t()); }
    if (possible.isEmpty()){ throw noCandidate(d,mat); }
    return Reason.callResultCannotHaveRequiredType(ts,d,c, req, bests(mat,possible),sig);
  }
  //Unique unless the minimal types are a bare 'X' and some 'rc X'. A bare X stands for its whole
  //bound, so those two are incomparable, but both are sound and the "As declared" one comes first.
  private T bestUnique(ArgMatrix mat, List<Integer> idxs){ return bests(mat,idxs).getFirst(); }
  private List<T> bests(ArgMatrix mat, List<Integer> idxs){
    var all= idxs.stream().map(i->mat.candidate(i).t()).toList();
    assert all.stream().allMatch(ti->all.stream().allMatch(tj->tj.equals(ti) || !ts.isSub(bs,tj,ti) || !ts.isSub(bs,ti,tj)));
    return all.stream()
      .filter(ti->all.stream().noneMatch(tj->
        !tj.equals(ti) && ts.isSub(bs,tj,ti)))
      .distinct().toList();
  }
}