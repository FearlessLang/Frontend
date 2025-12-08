package message;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import metaParser.NameSuggester;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix;
import typeSystem.ArgMatrix.*;
import typeSystem.Change;
import typeSystem.Change.*;
import typeSystem.Gamma.Binding;
import utils.Bug;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import core.*;
import core.E.*;
import static message.Err.disp;
import static message.Err.methodSig;

public final class TypeSystemErrors { private TypeSystemErrors(){}
  private static FearlessException withCallSpans(FearlessException ex, Call c){
    return ex.addSpan(Parser.span(c.pos(), c.name().s().length())).addSpan(c.span().inner);
  }
  public static FearlessException overrideMismatch(Sig sub, Sig sup, String reason){ return Err.of()
    .pMethodContext("Invalid override", sub, sub.origin().s())
    .conflictsWithMethodIn(sup)
    .line("Reason: "+reason)
    .ex().addSpan(sub.span().inner);
  }
  public static FearlessException unresolvedConflict(TName type, M m1, M m2){ return Err.of()
    .line("Unresolved multiple inheritance conflict in type "+disp(type.s())+".")
    .line("Method "+disp(m1.sig().m().s())+" is inherited from both "+disp(m1.sig().origin().s())+" and "+disp(m2.sig().origin().s())+".")
    .line("You must override this method explicitly to resolve the ambiguity.")
    .ex().addSpan(Parser.span(type.pos(), type.s().length()));
  }
  public static FearlessException notKinded(T t){ return Err.of()
    .line("Type "+disp(t)+" is not well-kinded.")
    .line("It violates reference capability constraints.")
    .ex().addSpan(Parser.span(getPos(t),1));//TODO: we need to add a Span method for the types somehow, but this will require look at the parser
  }
  private static Pos getPos(T t){//When that is done, we will not have this method any more.
    if (t instanceof T.RCC rcc){ return rcc.c().name().pos(); }
    return Pos.UNKNOWN;
  }
  public static FearlessException notAffine(String name, List<E.X> usages){ 
    var ex= Err.of()
      .line("Usage violation for parameter "+disp(name)+".")
      .line("An iso parameter must be either:")
      .line("- Captured in object literals.")
      .line("- Directly used at most once.")
      .ex();
    for (var x:usages){ ex.addSpan(Parser.span(x.pos(), x.name().length())); }
    return ex;
  }
  public static String makeErrResult(ArgMatrix mat, List<Integer> okProm, TRequirement req){
    String promos= okProm.stream().map(i->mat.candidate(i).promotion()).sorted().collect(Collectors.joining(", "));//TODO: use Join here
    return "Return requirement not met.\nExpected: "+disp(req.t())+".\nPromotions: "+promos+".";
  }
  public static FearlessException methodReceiverRcBlocksCall(Call c, RC recvRc, List<MType> promos){
    List<String> needed= promos.stream().map(MType::rc).distinct().sorted().map(Err::disp).toList();
    var e= Err.of()
      .pCallCantBeSatisfied(c)      
      .line("The receiver (the expression before the method name) has capability "+disp(recvRc)+".")
      .line(Join.of(needed,"This call requires a receiver with capability "," or ","."))
      .pReceiverPromotionFailures(promos);
    return withCallSpans(e.ex(), c);
  }
  public static FearlessException callableMethodAbstract(TSpan at, M got, RC receiver){
    var s= got.sig();
    var e= Err.of()
      .line("Abstract method is being called.")
      .line("Method: "+methodSig(s.m())+".")
      .line("Declared abstract in: "+disp(s.origin().s())+".")
      .line("Receiver capability at call site: "+receiver+".");
    return e.ex().addSpan(at.inner);
  }
  public static FearlessException methodHopelessArg(Call c, int argi, List<TRequirement> reqs, List<TResult> res, Optional<ArgDiag> diag){
    assert reqs.size() == res.size();
    return withCallSpans(Err.of().pHopelessArg(c,argi,reqs,res,diag).ex(), c);
  }
  public static FearlessException methodNotDeclared(Call c, core.E.Literal d){
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
          candidates.stream().filter(s->s.m().s().equals(n)).forEach(s->e.line("  - "+sigToStr(s)));
        }
        return e.text();
      });
      return withCallSpans(Code.TypeError.of(msg), c);
    }
    var sameArity= sameName.stream().filter(s->s.m().arity() == c.es().size()).toList();
    if (sameArity.isEmpty()){
      String avail= Join.of(sameName.stream().map(s->Integer.toString(s.m().arity())).distinct().sorted(), "", " or ", "");
      var e= Err.of()
        .pCallCantBeSatisfied(c) 
        .line("There is a method "+disp(c.name().s())+" on type "+disp(d.name().s())+", but with different number of arguments.")
        .line("This call supplies "+c.es().size()+", but available methods take "+avail+".");
      return withCallSpans(e.ex(), c);
    }
    String availRc= Join.of(sameArity.stream().map(s->s.rc().toString()).distinct().sorted(), "", " and ", "");
    var e= Err.of()
      .pCallCantBeSatisfied(c)
      .line(methodSig(c.name())+" exists on type "+disp(d.name().s())+", but not with the requested capability.")
      .line("This call requires the existence of a "+disp(c.rc().toString())+" method.")
      .line("Available capabilities for this method: "+disp(availRc)+".");
    return withCallSpans(e.ex(), c);
  }
  public static FearlessException methodArgsDisagree(Call c, ArgMatrix mat){
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
      int argi= IntStream.range(0,ac).filter(a->!mat.res(a,ci).success()).findFirst().getAsInt();
      e.pPromoFail(argi, mat.candidate(ci).promotion()).pFailCause(mat.res(argi,ci).reason());
    });
    return withCallSpans(e.ex(), c);
  }
  public static FearlessException typeError(E at, List<TResult> got, List<TRequirement> req){
    assert got.size() == req.size();
    var e= Err.of();
    for(int i= 0; i < got.size(); i++){
      var gi= got.get(i);
      if (gi.success()){ continue; }
      var ri= req.get(i);
      if (!ri.reqName().isEmpty()){ e.line("Requirement "+disp(ri.reqName())+"."); }
      String reason= gi.reason();
      if (reason.isEmpty()){ reason= gotMsg(gi.best(), ri.t()); }
      e.line(reason).blank();
    }
    return e.ex().addSpan(at.span().inner);
  }
  public static FearlessException uncallableMethodDeadCode(TSpan at, M got, Literal l){
    assert l.rc() == RC.imm || l.rc() == RC.read;
    var s= got.sig();
    assert s.rc() == RC.mut;
    int line= l.pos().line();
    String m= Err.methodSig(s.rc()+" ", s.m());
    String lit= bestName(l);
    return Err.of()
      .line("Method "+m+" can never be called (dead code).")
      .line("The object literal "+lit+" at line "+line+" is "+disp(l.rc())+".")
      .line("Method "+m+" requires a "+disp(RC.mut)+" receiver, which cannot be obtained from a "+disp(l.rc())+" object.")
      .line("Hint: remove the implementation of method "+m+".")
    .ex().addSpan(at.inner);
  }
  public static FearlessException methodTArgsArityError(Call c, int expected){
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
      .ex(), c);
  }  
  public static FearlessException methodReceiverNotRcc(Call c, T recvType){
    String name= switch(recvType){
      case T.X x -> disp(x.name());
      case T.RCX(var _, var x) -> disp(x.name());
      case T.ReadImmX(var x) -> disp(x.name());
      case T.RCC _-> { throw Bug.unreachable(); }
    };
  return withCallSpans(Err.of()
    .pCallCantBeSatisfied(c)
    .line("The receiver is the type parameter "+name+".")
    .line("Type parameters cannot be receivers of method calls.")
    .ex(), c);
}
  private static String sigToStr(Sig s){
    var bsS= Join.of(s.bs(),"[",",","]","");
    var tsS= Join.of(s.ts(),"(",",",")","");
    return s.rc()+" "+s.m()+bsS+tsS+":"+s.ret()+";";
  }
  public static FearlessException mCallFrame(M m, FearlessException fe){
    return fe.addFrame("the body of method "+methodSig(m.sig().m()), m.sig().span().inner);
  }
  public record ArgDiag(String x, T declared, Optional<T> got, Optional<T> expected, Why why, Note note, List<B> bs, List<String> fitsPromos){}
  public enum Note{
    NONE,
    DECLARED_OK_SOME_CALL_EXPECTED,
    DECLARED_OK_THIS_EXPECTED,
    DECLARED_NOT_OK_THIS_EXPECTED,
  }
  public interface IsSub{ boolean isSub(List<B> bs, T a, T b); }

  public static Optional<ArgDiag> argDiagForCallArg(E e, List<TRequirement> reqs, Function<String,Binding> bind, IsSub isSub, List<B> bs){
    if (!(e instanceof E.X x)){ return Optional.empty(); }//TODO: eventually this will not be optional but there will be support for all kinds of expressions
    var b= bind.apply(x.name());
    T declared= b.declared();
    Change cur= b.current();
    Optional<T> got= cur.view(); // empty if Drop
    var fits= reqs.stream()
      .filter(r->isSub.isSub(bs, declared, r.t()))
      .map(TRequirement::reqName).filter(s->!s.isEmpty())
      .distinct().sorted().toList();
    Note note= fits.isEmpty() ? Note.NONE : Note.DECLARED_OK_SOME_CALL_EXPECTED;
    return Optional.of(new ArgDiag(x.name(), declared, got, Optional.empty(), cur.why(), note, bs, fits)); 
  }
  public static ArgDiag argDiagMismatch(String x, T declared, T got, T expected, Why why, boolean declaredOkExpected, List<B> bs){
  Note note= declared.equals(got) 
    ? Note.NONE
    : declaredOkExpected 
    ? Note.DECLARED_OK_THIS_EXPECTED 
    : Note.DECLARED_NOT_OK_THIS_EXPECTED;
  return new ArgDiag(x, declared, Optional.of(got), Optional.of(expected), why, note, bs, List.of());
  }
  public static ArgDiag argDiagHidden(String x, T declared, T expected, Why why, boolean declaredOkExpected, List<B> bs){
    Note note= declaredOkExpected ? Note.DECLARED_OK_THIS_EXPECTED : Note.DECLARED_NOT_OK_THIS_EXPECTED;
    return new ArgDiag(x, declared, Optional.empty(), Optional.of(expected), why, note, bs, List.of());
  }

  public static ArgDiag argDiagNotAvailable(String x, T declared, Why why, List<B> bs){
    return new ArgDiag(x, declared, Optional.empty(), Optional.empty(), why, Note.NONE, bs,List.of());
  }
  public static FearlessException nameNotAvailable(E.X x, T declared, Why why, List<B> bs){
    var d= new ArgDiag(x.name(), declared, Optional.empty(), Optional.empty(), why, Note.NONE, bs, List.of());
    var e= Err.of()
      .line("The parameter "+disp(x.name())+" is not available here.")
      .pArgDiag(d);
    return e.ex().addSpan(x.span().inner);
  }
  public static String xMismatch(String x, T expected, T got, T declared, Why why, boolean declaredOk, List<B> bs){
    var d= argDiagMismatch(x, declared, got, expected, why, declaredOk, bs);
    return Err.of().pArgDiag(d).text();
  }
  public static String gotMsg(T got, T expected){
    return Err.of().lineGotMsg(got, expected).text();
  }  
  public static Why strengthenToImm(T in){
    return (x, _, _, _, _)->"Viewpoint adaptation strengthened "+disp(x)+" to imm.";
  }
  public static Why setToRead(T in){
    return (x, _, got, declared, _)->got
      .<String>map(g->"Viewpoint adaptation set "+disp(x)+" to "+disp(g)+" from "+disp(declared)+" (the declared type).")
      .orElse("");
  }
  public static Why useReadImm(T in){
    return (x, _, _, _, _)->"Viewpoint adaptation replaced "+disp(x)+" with readImm(x).";
  }
  public static Why weakenedToRead(T in){
    return (x, _, _, _, _)->"Viewpoint adaptation weakened "+disp(x)+" to read.";
  }
  // in TypeSystemErrors (same "shown/instance" problem; also avoid precomputing outside the lambda)
  public static Why filterFTVWhy(Literal l, T atDrop){ return (x, _, _, _, _)->{
    String lit= bestName(l);
    var scope= l.bs().stream().map(B::x).distinct().sorted().toList();
    var scopeSet= new HashSet<>(scope);
    var ftv= new HashSet<String>();
    addFtv(atDrop, ftv);
    var missing= ftv.stream().filter(v->!scopeSet.contains(v)).sorted().map(Err::disp).toList();
    assert !missing.isEmpty();
    int line= l.pos().line();
    String where= "inside "+lit+ "(line "+line+").\n";
    return disp(x)+" cannot be captured "+where
      + "Here "+disp(x)+" has type "+disp(atDrop)+Join.of(missing,", which mentions type variable(s) "," and ",".\n")
      + "Add those type variables to the object literal header.";
  };} 
  private static void addFtv(T t, HashSet<String> out){ switch(t){
    case T.X x -> out.add(x.name());
    case T.RCX(_, var x) -> out.add(x.name());
    case T.ReadImmX(var x) -> out.add(x.name());
    case T.RCC(_, var c) -> c.ts().forEach(ti->addFtv(ti,out));
  }}
  public static Why discardWhy(Literal l, M m, T atDrop){ return (x, _, _, _, _)->{
    boolean bad= l.rc() == RC.iso || l.rc() == RC.imm;
    int line= m.sig().span().inner.startLine();
    String ms= methodSig(m.sig().rc()+" ", m.sig().m());
    String lit= bestName(l); 
    String base= disp(x)+" cannot be captured in the method body of "+ms+" (line "+line+" inside "+lit+").\n";
    if (bad){
      return base
        + "The literal "+lit+" is "+disp(l.rc())+", thus "+disp(atDrop)+" cannot be captured inside of it.\n"
        + "Hint: capture an immutable copy instead, or move this use outside the object literal.\n";
    }
    return base+disp(atDrop)
      + " violates reference capability constraints here, so the parameter is not available.";
  };}
  //Sadly no other way to guess if it was anonymous (maybe using Source oracle and the position to peek if the name is there, but brittle, comments and strings could be false positives.
  private static boolean isAnon(Literal l){ return l.name().simpleName().startsWith("_"); }
  private static String bestName(Literal l){ return !isAnon(l) ? disp(l.name().s()) : "instance of "+disp(l.cs().getFirst().name().s()); } 
}