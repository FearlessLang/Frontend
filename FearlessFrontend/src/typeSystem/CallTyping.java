package typeSystem;

import java.util.List;
import java.util.ArrayList;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import java.util.EnumSet;
import core.*;
import core.E.*;
import inject.TypeRename;
import message.TypeSystemErrors;
import utils.OneOr;
import utils.Push;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix.*;

record CallTyping(TypeSystem ts, List<B> bs, Gamma g, Call c, List<TRequirement> rs){
  List<TResult> run(){
    var rcc0= recvRcc();
    var d= ts.decs().apply(rcc0.c().name());
    var sig= sigOf(d);
    checkTargsKinding(rcc0.c(),d,sig);
    var base= baseMType(rcc0.c(),d,sig);
    var promos= ts.multiMeth(bs,base);
    var app= promos.stream().filter(m->rcc0.rc().isSubType(m.rc())).toList();
    if (app.isEmpty()){ throw TypeSystemErrors.methodReceiverRcBlocksCall(c,rcc0.rc(),promos); }
    var mat= typeArgsOnce(app);
    var possible= mat.candidatesOkForAllArgs();//This is indexes of MTypes allowed by the arguments
    if (possible.isEmpty()){ throw TypeSystemErrors.methodArgsDisagree(c,mat); }
    if (rs.isEmpty()){ return List.of(bestNoReq(mat,possible)); }
    return rs.stream().map(req->resForReq(mat,possible,req)).toList();
  }
  private T.RCC recvRcc(){
    var r= ts.typeOf(bs,g,c.e(),List.of());
    assert r.size() == 1;
    assert r.getFirst().success();//else would have thrown
    T t= r.getFirst().best();
    if (t instanceof T.RCC x){ return x; }
    throw TypeSystemErrors.methodReceiverNotRcc(c,t);
  }
  private Sig sigOf(Literal d){
    var ms= d.ms().stream().map(M::sig)
      .filter(s->s.m().equals(c.name()) && s.rc() == c.rc()).toList();
    if (ms.isEmpty()){ throw TypeSystemErrors.methodNotDeclared(c,d); }
    assert ms.size() == 1 : "Duplicate cached sig for "+c.name()+" rc="+c.rc()+" in "+d.name();
    Sig sig= ms.getFirst();
    assert sig.ts().size() == c.es().size();//ensured by well formedness
    if (sig.bs().size() == c.targs().size()){ return sig; }
    throw TypeSystemErrors.methodTArgsArityError(c);
  } 
  private MType baseMType(T.C c0, Literal d, Sig sig){
    var xs= Stream.concat(d.bs().stream(),sig.bs().stream()).map(B::x).toList();
    var ts0= Push.of(c0.ts(),c.targs());
    var ps= TypeRename.ofT(sig.ts(),xs,ts0);
    T ret= TypeRename.of(sig.ret(),xs,ts0);
    return new MType("`As declared`",sig.rc(),ps,ret);
  }
  private void checkTargsKinding(T.C c0, Literal d, Sig sig){
    assert c0.ts().size() == d.bs().size();
    var targs= c.targs();
    for(int i= 0; i < targs.size(); i++){
      ts.k().check(bs,targs.get(i),EnumSet.copyOf(sig.bs().get(i).rcs()));
    }
  }
  private ArgMatrix typeArgsOnce(List<MType> app){
    var size= c.es().size();
    var acc= new ArgMatrix(app,new ArrayList<>(size),new ArrayList<>(size));
    for (int argi= 0; argi < size; argi++){ accArgi(app,acc,c.es(), argi); }
    return acc;
  }
  private void accArgi(List<MType> app, ArgMatrix acc, List<E> es, int argi){
    var reqs= argRequirements(app,argi);
    var res= ts.typeOf(bs,g,es.get(argi),reqs);
    assert res.size() == app.size();
    var ok= okSet(res);
    if (ok.isEmpty()){ throw TypeSystemErrors.methodHopelessArg(c,argi,reqs,res); }
    acc.okByArg().add(ok);
    acc.resByArg().add(res);
  }
  private List<TRequirement> argRequirements(List<MType> app, int argi){
    return app.stream().map(m->new TRequirement(m.promotion(),m.ts().get(argi))).toList();
  }
  private static List<Integer> okSet(List<TResult> res){
    return IntStream.range(0,res.size()).filter(i->res.get(i).success()).boxed().toList();
  }
  private TResult bestNoReq(ArgMatrix mat, List<Integer> possible){ return new TResult("",bestUnique(mat,possible),""); }
  private TResult resForReq(ArgMatrix mat, List<Integer> possible, TRequirement req){
    var okRet= possible.stream()
      .filter(i->ts.isSub(bs,mat.candidate(i).t(),req.t())).toList();
    if (!okRet.isEmpty()){ return new TResult(req.reqName(), bestUnique(mat,okRet),""); }
    return new TResult(req.reqName(),bestUnique(mat,possible),
      TypeSystemErrors.makeErrResult(mat, possible, req));    
  } 
  private T bestUnique(ArgMatrix mat, List<Integer> idxs){
    List<T> all= idxs.stream().map(i->mat.candidate(i).t()).toList();
    return OneOr.of("noUniqueBest", all.stream()
      .filter(ti->all.stream().noneMatch(tj->
        !tj.equals(ti) && ts.isSub(bs,tj,ti)))
      .distinct());
  }
}