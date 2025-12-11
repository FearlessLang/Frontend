package typeSystem;

import java.util.List;
import java.util.ArrayList;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import java.util.EnumSet;
import core.*;
import core.E.*;
import inject.TypeRename;
import message.Reason;
import utils.OneOr;
import utils.Push;
import typeSystem.TypeSystem.*;

record CallTyping(TypeSystem ts, List<B> bs, Gamma g, Call c, List<TRequirement> rs){
  List<Reason> run(){
    var rcc0= recvRcc();
    var d= ts.decs().apply(rcc0.c().name());
    var sig= sigOf(d);
    checkTargsKinding(rcc0.c(),d,sig);
    var base= baseMType(rcc0.c(),d,sig);
    var promos= ts.multiMeth(bs,base);
    var app= promos.stream().filter(m->rcc0.rc().isSubType(m.rc())).toList();
    if (app.isEmpty()){ throw ts.err().receiverRCBlocksCall(c,rcc0.rc(),promos); }
    var mat= typeArgsOnce(app);
    var possible= mat.candidatesOkForAllArgs();//This is indexes of MTypes allowed by the arguments
    if (possible.isEmpty()){ throw ts.err().methodPromotionsDisagreeOnArguments(c,mat); }
    if (rs.isEmpty()){ return List.of(Reason.pass(bestUnique(mat,possible))); }
    return rs.stream().map(req->resForReq(mat,possible,req)).toList();
  }
  private T.RCC recvRcc(){
    var r= ts.typeOf(bs,g,c.e(),List.of());
    assert r.size() == 1;
    assert r.getFirst().isEmpty();//else would have thrown
    T t= r.getFirst().best;
    if (t instanceof T.RCC x){ return x; }
    throw ts.err().methodReceiverIsTypeParameter(c,t);
  }
  private Sig sigOf(Literal d){
    var ms= d.ms().stream().map(M::sig)
      .filter(s->s.m().equals(c.name()) && s.rc() == c.rc()).toList();
    if (ms.isEmpty()){ throw ts.err().methodNotDeclared(c,d); }
    assert ms.size() == 1 : "Duplicate cached sig for "+c.name()+" rc="+c.rc()+" in "+d.name();
    Sig sig= ms.getFirst();
    assert sig.ts().size() == c.es().size();//ensured by well formedness
    if (sig.bs().size() == c.targs().size()){ return sig; }
    throw ts.err().methodTArgsArityError(c,sig.bs().size());
  } 
  private MType baseMType(T.C c0, Literal d, Sig sig){
    var xs= Stream.concat(d.bs().stream(),sig.bs().stream()).map(B::x).toList();
    var ts0= Push.of(c0.ts(),c.targs());
    var ps= TypeRename.ofT(sig.ts(),xs,ts0);
    T ret= TypeRename.of(sig.ret(),xs,ts0);
    return new MType("As declared",sig.rc(),ps,ret);
  }
  private void checkTargsKinding(T.C c0, Literal d, Sig sig){
    assert c0.ts().size() == d.bs().size();
    var targs= c.targs();
    for(int i= 0; i < targs.size(); i++){
      ts.k().check(d,bs,targs.get(i),EnumSet.copyOf(sig.bs().get(i).rcs()));
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
    if (ok.isEmpty()){
      throw ts.err().methodArgumentCannotMeetAnyPromotion(c,argi,reqs,res);
    }
    acc.okByArg().add(ok);
    acc.resByArg().add(res);
  }
  private List<TRequirement> argRequirements(List<MType> app, int argi){
    return app.stream().map(m->new TRequirement(m.promotion(),m.ts().get(argi))).toList();
  }
  private static List<Integer> okSet(List<Reason> res){
    return IntStream.range(0,res.size()).filter(i->res.get(i).isEmpty()).boxed().toList();
  }
  private Reason resForReq(ArgMatrix mat, List<Integer> possible, TRequirement req){
    List<Integer> okRet= possible.stream()
      .filter(i->ts.isSub(bs,mat.candidate(i).t(),req.t())).toList();
    if (!okRet.isEmpty()){ return Reason.pass(req.reqName(), bestUnique(mat,okRet)); }
    return Reason.callResultCannotHaveRequiredType(c, bs, mat, possible, req,bestUnique(mat,possible));
  } 
  private T bestUnique(ArgMatrix mat, List<Integer> idxs){
    List<T> all= idxs.stream().map(i->mat.candidate(i).t()).toList();
    return OneOr.of("noUniqueBest", all.stream()
      .filter(ti->all.stream().noneMatch(tj->
        !tj.equals(ti) && ts.isSub(bs,tj,ti)))
      .distinct());
  }
}