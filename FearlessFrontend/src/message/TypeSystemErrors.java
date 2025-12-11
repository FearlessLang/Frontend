package message;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import metaParser.Message;
import metaParser.NameSuggester;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix;
import typeSystem.Change;
import utils.Bug;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import core.*;
import core.E.*;
import static message.Err.disp;
import static message.Err.methodSig;

public record TypeSystemErrors(pkgmerge.Package pkg){
  private FearlessException withCallSpans(FearlessException ex, Call c){
    return ex.addSpan(Parser.span(c.pos(), c.name().s().length())).addSpan(c.span().inner);
  }
  public FearlessException overrideMismatch(Literal l,Sig sub, Sig sup, String reason){ return Err.of()
    .pMethodContext("Invalid override", sub, sub.origin().s())
    .conflictsWithMethodIn(sup)
    .line("Reason: "+reason)
    .ex(pkg, l).addSpan(sub.span().inner);
  }
  public FearlessException unresolvedConflict(Literal l, TName type, M m1, M m2){ return Err.of()
    .line("Unresolved multiple inheritance conflict in type "+disp(type.s())+".")
    .line("Method "+disp(m1.sig().m().s())+" is inherited from both "+disp(m1.sig().origin().s())+" and "+disp(m2.sig().origin().s())+".")
    .line("You must override this method explicitly to resolve the ambiguity.")
    .ex(pkg,l).addSpan(Parser.span(type.pos(), type.s().length()));
  }
  public FearlessException notKinded(E toErr, T t){ return Err.of()
    .line("Type "+disp(t)+" is not well-kinded.")
    .line("It violates reference capability constraints.")
    .ex(pkg,toErr)
    .addSpan(Parser.span(getPos(t),1))
    .addSpan(toErr.span().inner);
  }
  private Pos getPos(T t){//When that is done, we will not have this method any more.
    if (t instanceof T.RCC rcc){ return rcc.c().name().pos(); }
    return Pos.UNKNOWN;
  }
  public FearlessException notAffine(M m, String name, List<E.X> usages){ 
    var ex= Err.of()
      .line("Usage violation for parameter "+disp(name)+".")
      .line("An iso parameter must be either:")
      .line("- Captured in object literals.")
      .line("- Directly used at most once.")
      .ex(pkg, m.e().get());
    for (var x:usages){ ex.addSpan(Parser.span(x.pos(), x.name().length())); }
    return ex;
  }
  public String makeErrResult(ArgMatrix mat, List<Integer> okProm, TRequirement req){
    String promos= okProm.stream().map(i->mat.candidate(i).promotion()).sorted().collect(Collectors.joining(", "));//TODO: use Join here
    return "Return requirement not met.\nExpected: "+disp(req.t())+".\nPromotions: "+promos+".";
  }
  
  public FearlessException methodReceiverRcBlocksCall(Call c, RC recvRc, List<MType> promos){
    List<String> needed= promos.stream().map(MType::rc).distinct().sorted().map(Err::disp).toList();
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(c)      
      .line("The receiver (the expression before the method name) has capability "+disp(recvRc)+".")
      .line(Join.of(needed,"This call requires a receiver with capability "," or ","."))
      .pReceiverRequiredByPromotion(promos)
      .ex(pkg,c), c);
  }
  public FearlessException callableMethodAbstract(TSpan at, M got, Literal l){
    var s= got.sig();
    return Err.of()
      .line("Abstract method is being called.")//TODO: NO, this does not make any sense
      .line("Method: "+methodSig(s.m())+".")
      .line("Declared abstract in: "+disp(s.origin().s())+".")
      .line("Literal capability: "+l.rc()+".")
      .ex(pkg,l).addSpan(at.inner);
  }
  public FearlessException methodHopelessArg(Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    throw Bug.todo();/*assert reqs.size() == res.size();
    return withCallSpans(Err.of()
      .pHopelessArg(c,argi,reqs,res,diag)
      .ex(pkg,c), c);
      */
  }
  public FearlessException methodNotDeclared(Call c, core.E.Literal d){
    String name= c.name().s();
    var candidates= d.ms().stream().map(M::sig).toList();
    var sameName= candidates.stream().filter(s->s.m().s().equals(name)).toList();
    if (sameName.isEmpty()){
      var names= candidates.stream().map(s->s.m().s()).distinct().sorted().toList();
      var msg= NameSuggester.suggest(name, names, (_, cs, best) -> {//TODO: all the name suggester stuff clearly need to go in Err.
        var e= Err.of()//Also, a lambda this long MUST be in its own method.
          .pCallCantBeSatisfied(c)
          .line("Such method is not declared on type "+disp(d.name().s())+".");
        best.ifPresent(b->e.line("Did you mean "+disp(b)+" ?"));
        if (cs.isEmpty()){ return e.line("The type "+disp(d.name().s())+" does not have any methods.").text(); }
        e.blank().line("Available methods:");
        for (String n:cs){
          candidates.stream().filter(s->s.m().s().equals(n)).forEach(s->e.bullet(sigToStr(s)));
        }
        return e.text();
      });
      return withCallSpans(Code.TypeError.of(msg), c);
    }
    var sameArity= sameName.stream().filter(s->s.m().arity() == c.es().size()).toList();
    if (sameArity.isEmpty()){
      String avail= Join.of(sameName.stream().map(s->Integer.toString(s.m().arity())).distinct().sorted(), "", " or ", "");
      return withCallSpans(Err.of()
        .pCallCantBeSatisfied(c) 
        .line("There is a method "+disp(c.name().s())+" on type "+disp(d.name().s())+", but with different number of arguments.")
        .line("This call supplies "+c.es().size()+", but available methods take "+avail+".")
        .ex(pkg,c), c);
    }
    String availRc= Join.of(sameArity.stream().map(s->s.rc().toString()).distinct().sorted(), "", " and ", "");
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(c)
      .line(methodSig(c.name())+" exists on type "+disp(d.name().s())+", but not with the requested capability.")
      .line("This call requires the existence of a "+disp(c.rc().toString())+" method.")
      .line("Available capabilities for this method: "+disp(availRc)+".")
      .ex(pkg,c), c);
  }
  public FearlessException methodArgsDisagree(Call c, ArgMatrix mat){
    int ac= mat.aCount();
    int cc= mat.cCount();
    var e= Err.of()
      .pCallCantBeSatisfied(c)
      .pArgsDisagreeIntro();
    for(int argi= 0; argi < ac; argi++){
      List<String> ok= mat.okForArg(argi).stream().map(ci->mat.candidate(ci).promotion()).distinct().sorted().toList();
      e.pAcceptedByPromos(argi, ok);
    }
    e.pPromotionFailuresHdr();
    IntStream.range(0,cc).forEach(ci->{
      int argi= IntStream.range(0,ac).filter(a->!mat.res(a,ci).isEmpty()).findFirst().getAsInt();
      e.pPromoFailure(mat.res(argi,ci).info, mat.candidate(ci).promotion());
    });
    return withCallSpans(e.ex(pkg,c), c);
  }
  public FearlessException typeError(E at, List<Reason> got, List<TRequirement> req){
    assert got.size() == req.size();
    var e= Err.of();
    for(int i= 0; i < got.size(); i++){
      var gi= got.get(i);
      if (gi.isEmpty()){ continue; }
      var ri= req.get(i);//TODO: this requirment never prints
      if (!ri.reqName().isEmpty()){ e.line("@@Requirement "+disp(ri.reqName())+"."); }
      String reason= gi.info;
      if (reason.isEmpty()){ reason= gotMsg(gi.best, ri.t()); }
      e.line(reason);
    }
    return e.ex(pkg,at).addSpan(at.span().inner);
  }
  public String gotMsg(T got, T expected){
    String g= Message.displayString(got.toString());
    String e= Message.displayString(expected.toString());
    return g+" is not a subtype of "+e+".";
  }
  public FearlessException uncallableMethodDeadCode(TSpan at, M got, Literal l){
    assert l.rc() == RC.imm || l.rc() == RC.read;
    var s= got.sig();
    assert s.rc() == RC.mut;
    int line= l.pos().line();
    String m= Err.methodSig(s.rc()+" ", s.m());
    String lit= Reason.bestName(l);
    return Err.of()
      .line("Method "+m+" can never be called (dead code).")
      .line("The object literal "+lit+" at line "+line+" is "+disp(l.rc())+".")
      .line("Method "+m+" requires a "+disp(RC.mut)+" receiver, which cannot be obtained from a "+disp(l.rc())+" object.")
      .line("Hint: remove the implementation of method "+m+".")
      .ex(pkg,l).addSpan(at.inner);
  }
  public FearlessException methodTArgsArityError(Call c, int expected){
    int got= c.targs().size(); assert got != expected;
    String expS= expected == 0 
      ? "no type arguments" 
      : expected+" type argument"+(expected == 1 ? "" : "s");
    String gotS= got == 0 
      ? "no type arguments" 
      : got+" type argument"+(got == 1 ? "" : "s");
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(c)
      .line("Wrong number of type arguments for "+methodSig(c.name())+".")
      .line("This method expects "+expS+", but this call provides "+gotS+".")
      .ex(pkg,c), c);
  }  
  public FearlessException methodReceiverNotRcc(Call c, T recvType){
    String name= switch(recvType){
      case T.X x -> disp(x.name());
      case T.RCX(var _, var x) -> disp(x.name());
      case T.ReadImmX(var x) -> disp(x.name());
      case T.RCC _-> { throw Bug.unreachable(); }
    };
  return withCallSpans(Err.of()
    .pCallCantBeSatisfied(c)
    .line("The receiver is of type "+name+". This is a type parameter.")
    .line("Type parameters cannot be receivers of method calls.")
    .ex(pkg,c), c);
  }
  private String sigToStr(Sig s){
    var bsS= Join.of(s.bs(),"[",",","]","");
    var tsS= Join.of(s.ts(),"(",",",")","");
    return s.rc()+" "+s.m()+bsS+tsS+":"+s.ret()+";";
  }
  public FearlessException mCallFrame(M m, FearlessException fe){
    return fe.addFrame(methodSig(m.sig().m())+" line "+m.sig().span().inner.startLine(), m.sig().span().inner);
  }
  public interface IsSub{ boolean isSub(List<B> bs, T a, T b); }
  
  
  public FearlessException nameNotAvailable(E.X x, T declared, Change why, List<B> bs){
    throw Bug.of();/*var d= new ArgDiag(x.name(), declared, Optional.empty(), Optional.empty(), why, Note.NONE, bs, List.of());
    return Err.of()
      .line("The parameter "+disp(x.name())+" is not available here.")
      .blank()
      .pArgDiag(d)
      .ex(pkg,x)
      .addSpan(x.span().inner);*/
  }
}