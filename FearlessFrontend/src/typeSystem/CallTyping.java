package typeSystem;

import java.util.List;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;
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
    checkTargsKinding(rcc0.c(), d, sig);
    var base= baseMType(rcc0.c(), d, sig);
    c.expectedRes().inner = base.t();
    var promos= MultiMeth.of(bs, base, true);
    var app= promos.stream().filter(m -> rcc0.rc().isSubType(m.rc())).toList();
    if (app.isEmpty()){ throw ts.tsE().receiverRCBlocksCall(d, c, rcc0.rc(), MultiMeth.of(bs, base, mayBeH(rcc0.rc(), base))); }
    var mat= typeArgsOnce(d, rcc0.rc(), base, app);
    var possible= mat.candidatesOkForAllArgs();//This is indexes of MTypes allowed by the arguments
    if (possible.isEmpty()){ throw ts.tsE().methodPromotionsDisagreeOnArguments(c, mat); }
    if (rs.isEmpty()){ return List.of(Reason.pass(bestUnique(mat, possible))); }
    return rs.stream().map(req -> resForReq(d, sig, mat, possible, req)).toList();
  }
  private boolean mayBeH(RC recv, MType base){
    return recv.isH() || Push.of(base.ts(), base.t()).stream().anyMatch(this::mayBeH);
  }
  private boolean mayBeH(T t){
    if (t instanceof T.X(var name, _)){ return B.get(bs, name).rcs().stream().anyMatch(RC::isH); }
    return t.explicitH();
  }
  private T.RCC recvRcc(){
    var cts= new TypeSystem(ts.scope().pushCallRec(this.c), ts.v());
    var r= OneOr.of("One reason without requirements", cts.typeOf(bs, g, c.e(), List.of()).stream());
    assert r.isEmpty();//else would have thrown
    var t= r.best;
    if (t instanceof T.RCC x){ return x; }
    throw ts.tsE().methodReceiverIsTypeParameter(cts.scope(), c, t);
  }
  private Sig sigOf(Literal d){
    var sig= OneOr.opt("Methods with duplicates", d.ms().stream().map(M::sig)
      .filter(s -> s.m().equals(c.name()) && s.rc() == c.rc()))
      .orElseThrow(() -> ts.tsE().methodNotDeclared(ts.scope(), c, d));
    assert sig.ts().size() == c.es().size();//ensured by well formedness
    if (sig.bs().size() == c.targs().size()){ return sig; }
    throw ts.tsE().methodTArgsArityError(d, c, sig.bs());
  }
  private MType baseMType(T.C c0, Literal d, Sig sig){
    var xs= B.xs(Push.of(d.bs(), sig.bs()));
    var ts0= Push.of(c0.ts(), c.targs());
    var ps= TypeRename.ofT(sig.ts(), xs, ts0);
    var ret= TypeRename.of(sig.ret(), xs, ts0);
    return new MType("As declared", sig.rc(), ps, ret);
  }
  private void checkTargsKinding(T.C c0, Literal d, Sig sig){
    assert c0.ts().size() == d.bs().size();
    var targs= c.targs();
    var kt= new KindingTarget.CallKinding(c0, c);
    for (int i : Range.of(targs)){
      ts.k().check(c, kt, i, bs, targs.get(i), sig.bs().get(i).rcs());
    }
  }
  private ArgMatrix typeArgsOnce(Literal d, RC recv, MType base, List<MType> app){
    var size= c.es().size();
    var acc= new ArgMatrix(app, new ArrayList<>(size), new ArrayList<>(size));
    for (int argi : Range.of(0, size)){ accArgi(d, recv, base, acc, argi); }
    return acc;
  }
  private List<TRequirement> argRequirements(List<MType> app, int argi){
    return app.stream()
      .collect(Collectors.groupingBy(m -> m.ts().get(argi), LinkedHashMap::new, Collectors.mapping(MType::promotion, Collectors.joining(", "))))
      .entrySet().stream().map(e -> new TRequirement(e.getValue(), e.getKey())).toList();
  }
  private void accArgi(Literal d, RC recv, MType base, ArgMatrix acc, int argi){
    var reqs= argRequirements(acc.cs(), argi);
    var cts= new TypeSystem(ts.scope().pushCallArgi(this.c, argi), ts.v());
    var resByReq= cts.typeOf(bs, g, c.es().get(argi), reqs);
    assert resByReq.size() == reqs.size();
    if (resByReq.stream().noneMatch(Reason::isEmpty)){ throw argCannotMeetAnyPromotion(cts, d, recv, base, acc, argi, reqs, resByReq); }
    var reqTs= reqs.stream().map(TRequirement::t).toList();
    var res= acc.cs().stream().map(m -> resByReq.get(reqTs.indexOf(m.ts().get(argi)))).toList();
    acc.okByArg().add(IntStream.range(0, res.size()).filter(i -> res.get(i).isEmpty()).boxed().toList());
    acc.resByArg().add(res);
  }
  private FearlessException argCannotMeetAnyPromotion(TypeSystem cts, Literal d, RC recv, MType base, ArgMatrix acc, int argi, List<TRequirement> reqs, List<Reason> resByReq){
    var args= Stream.concat(acc.resByArg().stream().flatMap(List::stream), resByReq.stream());
    if (mayBeH(recv, base) || args.anyMatch(r -> mayBeH(r.best))){ return cts.tsE().methodArgumentCannotMeetAnyPromotion(cts, bs, d, c, argi, reqs, resByReq); }
    var reqTs= reqs.stream().map(TRequirement::t).toList();
    var shown= argRequirements(MultiMeth.of(bs, base, false).stream().filter(m -> recv.isSubType(m.rc())).toList(), argi);
    var res= shown.stream().map(q -> resByReq.get(reqTs.indexOf(q.t()))).toList();
    return cts.tsE().methodArgumentCannotMeetAnyPromotion(cts, bs, d, c, argi, shown, res);
  }
  private Reason resForReq(Literal d, Sig sig, ArgMatrix mat, List<Integer> possible, TRequirement req){
    var okRet= possible.stream()
      .filter(i -> ts.isSub(bs, mat.candidate(i).t(), req.t())).toList();
    if (!okRet.isEmpty()){ return Reason.pass(bestUnique(mat, okRet)); }
    return Reason.callResultCannotHaveRequiredType(ts, d, c, req, bests(mat, possible), sig);
  }
  //Unique unless the minimal types are a bare 'X' and some 'rc X'. A bare X stands for its whole
  //bound, so those two are incomparable, but both are sound and the "As declared" one comes first.
  private T bestUnique(ArgMatrix mat, List<Integer> idxs){ return bests(mat, idxs).getFirst(); }
  private List<T> bests(ArgMatrix mat, List<Integer> idxs){
    var all= idxs.stream().map(i -> mat.candidate(i).t()).toList();
    assert all.stream().allMatch(ti -> all.stream().allMatch(tj -> tj.equals(ti) || !ts.isSub(bs, tj, ti) || !ts.isSub(bs, ti, tj)));
    return all.stream()
      .filter(ti -> all.stream().noneMatch(tj ->
        !tj.equals(ti) && ts.isSub(bs, tj, ti)))
      .distinct().toList();
  }
}