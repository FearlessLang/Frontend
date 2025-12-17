package message;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import metaParser.NameSuggester;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix;
import typeSystem.Change;
import typeSystem.TypeScope;
import typeSystem.TypeSystem;
import utils.Bug;
import utils.OneOr;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import core.*;
import core.E.*;

import static message.Err.*;

public record TypeSystemErrors(Function<TName,Literal> decs,pkgmerge.Package pkg){
  private FearlessException addExpFrame(E toErr,FearlessException err){
    return err.addFrame(expRepr(toErr),toErr.span().inner);
    }
  private FearlessException overrideErr(Literal l, Sig sub, Err e){
    return addExpFrame(l, e.ex(pkg, l).addSpan(sub.span().inner));
  }
  ///Fired when a generic instantiation Id[Ts] does not respect the RC bounds
  ///declared in Id[Bs]. This is a "type arguments vs generic header" error,
  ///not a method-resolution or expression-typing error.
  ///Raised when checking types anywhere they appear.
  public FearlessException typeNotWellKinded(E toErr, KindingTarget target, int index, EnumSet<RC> bounds){
    assert index >= 0;
    String allowedStr= Join.of(bounds.stream().map(Err::disp).sorted(), "", " or ", "");
    Err err=switch(target){
      case T.RCC rcc -> typeNotWellKinded("type "+disp(rcc),rcc.c(), index, allowedStr);
      case T.C c -> typeNotWellKinded("type "+disp(c),c, index, allowedStr);
      case KindingTarget.CallKinding(var t,var c)   -> typeNotWellKindedSig(t,c, index, allowedStr);
    };
    return addExpFrame(toErr,err.ex(pkg, toErr).addSpan(target.span().inner));
  }
  private Err typeNotWellKinded(String name,T.C c, int index, String allowedStr){
    var args= c.ts();
    assert index >= 0 && index < args.size();
    T bad= args.get(index);
    var bs= decs.apply(c.name()).bs();
    assert index < bs.size();
    String typeName = disp(c.name().s());
    String paramName= disp(bs.get(index).x());
    return Err.of().pTypeArgBounds(name, typeName, paramName, index, disp(bad), allowedStr);
  }
  private Err typeNotWellKindedSig(T.C t, E.Call c, int index, String allowedStr){
    var ms= decs.apply(t.name()).ms();
    var m= OneOr.of("Malformed methods",ms.stream().filter(mi->mi.sig().m().equals(c.name()) && mi.sig().rc() == c.rc()));
    var bs= m.sig().bs();
    assert index >= 0 && index < bs.size();
    var param= bs.get(index);
    String decName   = methodSig(t.name(), c.name()); // p.A.m(...)
    T bad            = c.targs().get(index);
    return Err.of().pTypeArgBounds("call to "+methodSig(c.name()), decName, disp(param.x()), index, disp(bad), allowedStr);
  } 
  ///Overriding method in literal l is not a valid subtype of inherited method.
  ///Raised when checking object literals
  public FearlessException methodOverrideSignatureMismatchContravariance(Literal l, Sig current, Sig parent, int index){
    var mName= current.m();
    assert mName.equals(parent.m());  
    assert index >= 0 && index < current.ts().size() && index < parent.ts().size();
    T parentArg= parent.ts().get(index);
    T currentArg= current.ts().get(index);
    return overrideErr(l, current, Err.of()
      .invalidMethImpl(l,mName)
      .line("The method "+methodSig(mName)+" accepts argument "+(index+1)+" of type "+disp(currentArg)+".")
      .line("But "+methodSig(parent.origin(),mName)+" requires "+Err.disp(parentArg)+", which is not a subtype of "+disp(currentArg)+".")
    );
  }
  ///Overriding method in literal l is not a valid subtype of inherited method.
  ///Raised when checking object literals
  public FearlessException methodOverrideSignatureMismatchCovariance(Literal l, Sig current, Sig parent){
    var mName=current.m();
    assert mName.equals(parent.m());
    T parentRet= parent.ret();
    T currentRet= current.ret();
    return overrideErr(l, current, Err.of()
      .invalidMethImpl(l,mName)
      .line("The method "+methodSig(mName)+" returns type "+disp(currentRet)+".")
      .line("But "+methodSig(parent.origin(),mName)+" returns type "+disp(parentRet)+", which is not a supertype of "+disp(currentRet)+".")
    );
  }
  ///A required method was left abstract instead of being implemented.
  ///Raised when checking object literals
  public FearlessException callableMethodStillAbstract(TSpan at, M got, Literal l){
    var s= got.sig();
    return addExpFrame(l, Err.of()
      .line("This object literal is missing a required method.")
      .line("Missing: "+methodSig(s.rc()+" ", s.m())+".")
      .line("Required by: "+typeDecNamePkg(s.origin())+".")
      .line("Hint: add an implementation for "+methodSig(s.m())+" inside the object literal.")
      .ex(pkg,l));
  }
  ///Implemented method can never be called for any receiver obtained from the literal.
  ///Its body is statically dead code (typically a mut method on an imm/read literal).
  ///Raised when checking object literals   
  public FearlessException methodImplementationDeadCode(TSpan at, M got, Literal l){
    var s= got.sig();
    assert s.rc() == RC.mut;
    assert l.rc() == RC.imm || l.rc() == RC.read;
    String m= methodSig(s.rc()+" ", s.m());
    return addExpFrame(l, Err.of()
      .line("The method "+methodSig(l,s.m())+" is dead code.")
      .line("The "+expRepr(l)+" is "+disp(l.rc())+", so it will never be seen as "+disp(RC.mut)+".")
      .line("But it implements method "+m+", which requires a "+disp(RC.mut)+" receiver.")
      .ex(pkg,l).addSpan(at.inner));
  }  
  ///Iso parameter is used in a way that violates affine discipline.
  ///Allowed uses: capture into object literals as imm, or use directly at most once.
  ///if !earlyErrOnMoreThenOnceDirectly then used exactly once directly but ALSO used in literals
  ///Raised when checking object literals
  public FearlessException notAffineIso(Literal l,M m, String name, boolean earlyErrOnMoreThenOnceDirectly, List<E.X> usages){
    assert !usages.isEmpty();
    int line= m.sig().span().inner.startLine();
    String ms= methodSig(l, m.sig().m());
    String x= disp(name);
    var e= Err.of()
      .line("Iso parameter "+x+" violates the single-use rule in method "+ms+" (line "+line+").");
    if (earlyErrOnMoreThenOnceDirectly){
      e.line("It is used directly "+usages.size()+" times.");
      e.line("Iso parameters can be used directly at most once.");
    } 
    else{
      e.line("It is used directly and also captured into object literals.");
      e.line("An iso parameter must be either captured, or used directly once (but not both).");
    }
    e.line("Allowed: capture into object literals as "+disp(RC.imm)+", or use directly once.");
    var ex= e.ex(pkg, m.e().get());
    for (var u:usages){ ex.addSpan(u.span().inner); }
    return ex;
  }
  ///Expression at method body has a type that does not meet its result requirement(s).
  ///"body has wrong type" error; can only trigger if all current-expressions at are well typed.
  ///Raised when checking object literals
  public FearlessException methBodyWrongType(TypeScope.Method s, E at, List<Reason> got, List<TRequirement> req){
    Literal l= s.l();
    M m= s.m();
    assert got.size() == req.size();
    assert got.stream().allMatch(r->!r.isEmpty());
    var got0= disp(got.getFirst().best);
    var req0= disp(req.getFirst().t());
    var e= Err.of();
    String meth= Err.methodSig(m.sig().m());
    var top= l.thisName().equals("this");
    if (top){ e.line("The body of method "+meth+" of "+expRepr(l)+" is an expression returning "+got0+"."); }
    else{ e.line("Method "+meth+" inside the "+Err.expRepr(l) + " (line "+l.span().inner.startLine()+")"
      +"\nis implemented with an expression returning "+got0+"."); }
    boolean promoMode= at instanceof E.Call
       && rcOnlyMismatch(got.getFirst().best, req.getFirst().t());
    if (!promoMode){ e.line(up(got.getFirst().info)); }
    else { 
      e.blank().pPromotionFailuresHdr();
      got.forEach(r->e.pPromoFailure(r.info,r.promNames));
    }
    var footer= got.getFirst().footerE.get();
    E ctx= footer.orElseGet(()->{//TODO: eventually It should be guarenteed to be there in any reason; then we can just call .get(); now is only there for call
      List<T> interest= TypeScope.interestFromDeclVsReq(s.m().sig().ret(), req.getFirst().t());
      var best= TypeScope.bestInterestingScope(s, interest);
      return best.contextE();});
    FearlessException ex= e.exInferMsg(pkg,ctx,req0);
    return addExpFrame(at, ex.addSpan(at.span().inner));
  }
  ///Parameter x is syntactically in scope but its value was dropped by viewpoint adaptation.
  ///Raised when a use of x occurs after capturing have made it unavailable.
  ///Raised when checking parameters.
  public FearlessException parameterNotAvailableHere(E.X x, T declared, Change.NoT why, List<B> bs){
    return addExpFrame(x,Err.of()
      .line(whyDrop(expRepr(x),why))
      .ex(pkg,x)
      .addSpan(x.span().inner));
  }
  private static String whyDrop(String subject, Change.NoT why){
    return why.<Supplier<String>>name(
      ()->whyDropMutInImm(subject,why),
      ()->whyDropReadHMutH(subject,why),
      ()->whyDropFTV(subject,why)
      ).get();
  }
  private static String whyDropMutInImm(String subject, Change.NoT why){
    return subject+" has type "+disp(why.atDrop())+".\n"
    + subject+" has a \"mut\" capability; thus it can not be captured in the "+disp(why.l().rc())+" "+expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+").";
  }
  private static String whyDropReadHMutH(String subject, Change.NoT why){
    String explicitH= why.atDrop().explicitH()
      ? "The type of "+subject+" is hygienic (readH or mutH)\n"
      : "The type of "+subject+" can be instantiated with hygienics (readH or mutH)\n";
    return subject+" has type "+disp(why.atDrop())+".\n"
    + explicitH+ "and thus it can not be captured in the "+expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+").\n";
  }
  private static String hintAddTypeParameter(Change.NoT why){
    var name= why.l().name().simpleName();
    var current= disp(Join.of(why.l().bs().stream().map(B::x),name+"[",",","]",name));
    var next= disp(Join.of(why.l().bs().stream().map(B::x),name+"[",",",",...]",name+"[...,...]"));
    return"Hint: change "+current+" by adding the missing type parameters: "+next;
  }
  private static String whyDropFTV(String subject, Change.NoT why){
    return subject+" has type "+disp(why.atDrop())+".\n"
    + subject+" uses type parameters that are not propagated\n"
    + "into "+expRepr(why.l())
    +" (line "+why.l().span().inner.startLine()+")"
    + " and thus it can not be captured.\n"
    + hintAddTypeParameter(why);
  }
  ///Receiver expression of call c is typed into a type parameter (X / RC X / read/imm X), not a concrete RC C.
  ///Methods cannot be called on type parameters, so this call can never resolve.
  ///Raised when checking method calls.
  public FearlessException methodReceiverIsTypeParameter(TypeScope s,Call c, T recvType){
    var best= TypeScope.bestInterestingScope(s, List.of(recvType));
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(c)
      .line("The receiver is of type "+disp(recvType)+". This is a type parameter.")
      .line("Type parameters cannot be receivers of method calls.")
      .exInferMsg(pkg,best.contextE(),disp(recvType)),c);
  }
  ///No method matches call c.
  ///Sub-errors for more clarity
  /// - no such name at all; searching for similar names with "Did you mean..."
  /// - method name exist but with different arity; error will list those other method signatures
  /// - method exists with right arity, but different receiver RCs; list those other method signatures
  ///Raised when checking method calls.
  public FearlessException methodNotDeclared(Call c, Literal d){
    var e= Err.of()
      .pCallCantBeSatisfied(c)
      .line("Method "+methodSig(c.name())+" is not declared on type "+bestNamePkg(d)+".");
    String name= c.name().s();
    var candidates= d.ms().stream().map(M::sig).toList();
    List<Sig> sameName= candidates.stream()
      .filter(s->s.m().s().equals(name)).toList();
    if (sameName.isEmpty()){
      if (candidates.isEmpty()){ e.line("The type "+bestNamePkg(d)+" does not have any methods."); }
      else{
        var names= candidates.stream().map(s->s.m().s()).distinct().sorted().toList();
        NameSuggester.suggest(name, names,(_,cs,best)->{ bestNameMsg(e,c, d, candidates, cs, best); return null; } );
      }
      return withCallSpans(e.ex(pkg, c), c);
    }
    var sameArity= sameName.stream().filter(s->s.m().arity() == c.es().size()).toList();
    if (sameArity.isEmpty()){
      String avail= Join.of(sameName.stream().map(s->Integer.toString(s.m().arity())).distinct().sorted(), "", " or ", "");
      return withCallSpans(Err.of()
        .pCallCantBeSatisfied(c) 
        .line("There is a method "+disp(c.name().s())+" on type "+bestNamePkg(d)+",\nbut with different number of arguments.")
        .line("This call supplies "+c.es().size()+", but available methods take "+avail+".")
        .ex(pkg,c), c);
    }
    String availRc= Join.of(sameArity.stream().sorted().map(s->disp(s.rc())), "", " and ", ".");
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(c)
      .line(methodSig(c.name())+" exists on type "+bestNamePkg(d)+", but not with the requested capability.")
      .line("This call requires the existence of a "+disp(c.rc())+" method.")
      .line("Available capabilities for this method: "+availRc)
      .ex(pkg,c), c);
  }
  void bestNameMsg(Err e,Call c, Literal d, List<Sig> candidates, List<String> cs, Optional<String> best){
    best.ifPresent(b->e.line("Did you mean "+disp(b)+" ?"));
    e.blank().line("Available methods on type "+bestNamePkg(d)+":");
    var print= Err.compactPrinter(pkg);
    for (String n:cs){
      candidates.stream()
        .filter(s->s.m().s().equals(n))
        .forEach(s->e.bullet(print.get().sig(s)));
    }
  }
  ///A method matching c by name / arity / RC exists, but c supplies the wrong number of type arguments.
  ///Triggered only for explicitly written [Ts]; inference never reaches this error.
  ///Raised when checking method calls.
  public FearlessException methodTArgsArityError(Literal d, Call c, int expected){
    int got= c.targs().size(); assert got != expected;
    String expS= expected == 0 
      ? "no type arguments" 
      : expected+" type argument"+(expected == 1 ? "" : "s");
    String gotS= got == 0 
      ? "no type arguments" 
      : got+" type argument"+(got == 1 ? "" : "s");
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(d,c)
      .line("Wrong number of type arguments for "+methodSig(c.name())+".")
      .line("This method expects "+expS+", but this call provides "+gotS+".")
      .ex(pkg,c), c);
  }
  ///Methods exist for call c, but the receiver capability is too weak for all the available promotions.
  ///No promotion accepts this receiver, so the call cannot succeed regardless of argument types.
  ///Raised when checking method calls.
  public FearlessException receiverRCBlocksCall(Literal d, Call c, RC recvRc, List<MType> promos){
    List<String> needed= promos.stream().map(MType::rc).distinct().sorted().map(Err::disp).toList();
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(d,c)
      .line("The receiver (the expression before the method name) has capability "+disp(recvRc)+".")
      .line(Join.of(needed,"This call requires a receiver with capability "," or ","."))
      .pReceiverRequiredByPromotion(promos)
      .ex(pkg,c), c);
  }
  ///For argument index argi in call c, the argument's type does not satisfy any promotion's requirement.
  ///Receiver and arguments are well typed, but this argument does not match any promotion.
  ///Sub-errors for more clarity
  /// - The argument type has the wrong nominal type, Person vs Car. In this case, promotions are not mentioned, just the general type mismatch.
  ///   This should also suppress detail from parameter Reason object
  /// - The argument best type met the intended nominal type, but the RC is off.
  ///   Here the Reason object should help to provide clarifications
  /// - Arguments return type is likely impacted by inference: argument is a generic method call or object literal
  ///   Do the Reason help here? if not, can we expand it or provide a parallel support?
  ///Raised when checking method calls.
  public FearlessException methodArgumentCannotMeetAnyPromotion(TypeSystem ts,List<B> bs, Literal d, Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    assert argi >= 0 && argi < c.es().size();
    assert !reqs.isEmpty();
    assert reqs.size() == res.size();
    assert res.stream().noneMatch(r->r.isEmpty());
    T reqCanon= reqCanon(reqs);
    if (isWrongUnderlyingType(ts,bs,reqCanon,res)){ return wrongUnderlyingTypeErr(ts.scope(),d,c,argi,reqs,res); }
    T gotHdr= headerBest(res);
    var any= reqs.stream().map(TRequirement::t).map(Err::disp).distinct().toList();
    var r= pickReason(reqs,res);
    var e= Err.of()
      .pCallCantBeSatisfied(d,c)
      .line("Argument "+(argi+1)+" has type "+disp(gotHdr)+".")
      .line(Join.of(any,"That is not a subtype of any of "," or ","."))
      .line(up(r.info))
      .blank()
      .line("Type required by each promotion:");
    var byT= new LinkedHashMap<T,List<String>>();
    for (var ri:reqs){ byT
      .computeIfAbsent(ri.t(),_->new ArrayList<>())
      .add(ri.reqName());
    }
    for (var ent:byT.entrySet()){
      var names= ent.getValue().stream().distinct().toList();
      e.bullet(disp(ent.getKey())+"  ("+Join.of(names,"",", ","")+")");
    }
    var footer= r.footerE.get();
    if (footer.isEmpty()){ return withCallSpans(e.ex(pkg, c), c); }
    return withCallSpans(e.exInferMsg(pkg,footer.get(),disp(reqs.getFirst().t())),c); 
  }
  private FearlessException wrongUnderlyingTypeErr(TypeScope s, Literal d, Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    T gotHdr= headerBest(res);//TODO: Eventually this will need to be matched with the meth body subtype and both 
    T required= reqs.getFirst().t(); //should make an attempt to say what the generics in the result should have been instantiate to instead
    //in particular here we are in a methCall, so we can talk about OUR type args impacting the expected argument type
    //TODO: line reqs.getFirst().t(); above, should we use the best return with ordering on rcs?
    var e= Err.of()          
      .pCallCantBeSatisfied(d,c)
      .line("Argument "+(argi+1)+" has type "+disp(gotHdr)+".")
      .line("That is not a subtype of "+disp(required)+".");
    return withCallSpans(e.ex(pkg, s.pushCallArgi(c,argi).contextE()), c);
  }
  private static T reqCanon(List<TRequirement> reqs){
    T c0= canon(reqs.getFirst().t());
    assert reqs.stream().allMatch(r->canon(r.t()).equals(c0));
    return c0;
  }
  private static boolean isWrongUnderlyingType(TypeSystem ts, List<B> bs, T reqCanon, List<Reason> res){
    return res.stream().map(r->canon(r.best)).noneMatch(r->ts.isSub(bs, r, reqCanon));
  }
  private static T canon(T t){ return t.withRC(fearlessParser.RC.imm); }

  private static T headerBest(List<Reason> res){
    return res.stream().map(r->r.best)
      .min(Comparator.comparingInt(TypeSystemErrors::headerKey))
      .orElseThrow();
  }
  private static int headerKey(T t){ return switch(t){
    case T.RCC r -> r.rc().ordinal();
    case T.RCX r -> r.rc().ordinal();
    case T.X _ -> 1000;
    case T.ReadImmX _ -> 1001;
  };}
  private static Reason pickReason(List<TRequirement> reqs, List<Reason> res){
    return res.get(IntStream.range(0, res.size())
      .filter(i->rcOnlyMismatch(res.get(i).best, reqs.get(i).t()))
      .findFirst().orElse(0));
  }  
  ///Each argument of call c is compatible with at least one promotion, but no promotion fits all arguments.
  ///The per-argument sets of acceptable promotions have empty intersection.
  ///Raised when checking method calls.
  ///Error details
  ///  - What arguments satisfy what promotion and why (best type <: required type1, required type 2 etc)  
  public FearlessException methodPromotionsDisagreeOnArguments(Call c, ArgMatrix mat){
    int args= mat.okByArg().size();
    assert args > 0 && mat.resByArg().size() == args;
    var e= Err.of()
      .pCallCantBeSatisfied(c)
      .line("Each argument is compatible with at least one promotion, but no single promotion fits all arguments.")
      .blank()
      .line("Compatible promotions by argument:");
    for (int argi= 0; argi < args; argi++){
      var ok= mat.okByArg().get(argi);
      assert !ok.isEmpty();
      var promos= ok.stream().map(i->mat.candidate(i).promotion()).distinct().sorted().toList();
      var got= disp(headerBest(mat.resByArg().get(argi)));
      e.bullet("Argument "+(argi+1)+" has type "+got+" and is compatible with: "+Join.of(promos,"",", ","")+".");
    }
    e.blank().pPromotionFailuresHdr();
    var byArg= IntStream.range(0,args)
      .mapToObj(_->new LinkedHashMap<String,List<String>>()).toList();
    int promosN= mat.resByArg().getFirst().size();
    for (int pi= 0; pi < promosN; pi++){
      int argi= firstFailingArg(mat, pi);
      Reason r= mat.resByArg().get(argi).get(pi);
      assert !r.isEmpty();
      byArg.get(argi).computeIfAbsent(up(r.info),_->new ArrayList<>())
        .add(mat.candidate(pi).promotion());
    }
    for (int argi= 0; argi < args; argi++){
      for (var ent: byArg.get(argi).entrySet()){
        var names= ent.getValue();
        e.pPromoFailure(
          "Argument "+(argi+1)+" fails:\n"+ent.getKey(),
          Join.of(names,"",", ","")
        );
      }
    }
  return withCallSpans(e.ex(pkg,c), c);
  }
  private static int firstFailingArg(ArgMatrix mat, int promoIdx){
    return IntStream.range(0, mat.okByArg().size())
      .filter(argi->!mat.okByArg().get(argi).contains(promoIdx))
      .findFirst().getAsInt();
  }

//---------------Utils

  private FearlessException withCallSpans(FearlessException ex, Call c){
    return ex.addSpan(Parser.span(c.pos(), c.name().s().length())).addSpan(c.span().inner);
  }
  public FearlessException override_Mismatch(Literal l,Sig sub, Sig parent, String reason){ return Err.of()
    .pMethodContext("Invalid override", sub, sub.origin().s())
    .conflictsWithMethodIn(parent)
    .line("Reason: "+reason)
    .ex(pkg, l).addSpan(sub.span().inner);
  }
  public FearlessException not_Kinded(E toErr, T t){ return Err.of()
    .line("Type "+disp(t)+" is not well-kinded.")
    .line("It violates reference capability constraints.")
    .ex(pkg,toErr)
    .addSpan(Parser.span(getPos(t),1))
    .addSpan(toErr.span().inner);
  }
  private Pos getPos(T t){//When that is done, we will not have this method any more.
    if (t instanceof T.RCC rcc){ return rcc.c().name().pos(); }
    throw Bug.of();
  }
  public FearlessException not_Affine(M m, String name, List<E.X> usages){ 
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
  
  public FearlessException methodReceiver_RcBlocksCall(Literal d,Call c, RC recvRc, List<MType> promos){
    List<String> needed= promos.stream().map(MType::rc).distinct().sorted().map(Err::disp).toList();
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(d,c)
      .line("The receiver (the expression before the method name) has capability "+disp(recvRc)+".")
      .line(Join.of(needed,"This call requires a receiver with capability "," or ","."))
      .pReceiverRequiredByPromotion(promos)
      .ex(pkg,c), c);
  }
  public FearlessException callableMethod_Abstract(TSpan at, M got, Literal l){
    throw Bug.todo();
  }
  public FearlessException methodHopeless_Arg(Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    throw Bug.todo();/*assert reqs.size() == res.size();
    return withCallSpans(Err.of()
      .pHopelessArg(c,argi,reqs,res,diag)
      .ex(pkg,c), c);
      */
  }
  public FearlessException meth_odNotDeclared(Call c, core.E.Literal d){
    throw Bug.todo();/*
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
      .ex(pkg,c), c);*/
  }
  public FearlessException methodArgs_Disagree(Literal d,Call c, ArgMatrix mat){
    int ac= mat.aCount();
    int cc= mat.cCount();
    var e= Err.of()
      .pCallCantBeSatisfied(d,c)
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
  public FearlessException type_Error(E at, List<Reason> got, List<TRequirement> req){
    assert got.size() == req.size();
    var e= Err.of();
    for(int i= 0; i < got.size(); i++){
      var gi= got.get(i);
      if (gi.isEmpty()){ continue; }
      var ri= req.get(i);//TODO: this requirment never prints
      if (!ri.reqName().isEmpty()){ e.line("@@Requirement "+disp(ri.reqName())+"."); }
      String reason= gi.info;
      if (reason.isEmpty()){ reason= Err.gotMsg(expRepr(at),gi.best, ri.t()); }
      e.line(reason);
    }
    return e.ex(pkg,at).addSpan(at.span().inner);
  }
  public FearlessException uncallableMethod_DeadCode(TSpan at, M got, Literal l){
    assert l.rc() == RC.imm || l.rc() == RC.read;
    var s= got.sig();
    assert s.rc() == RC.mut;
    int line= l.pos().line();
    String m= methodSig(s.rc()+" ", s.m());
    String lit= up(expRepr(l));
    return Err.of()
      .line("Method "+m+" can never be called (dead code).")
      .line(lit+" at line "+line+" is "+disp(l.rc())+".")
      .line("Method "+m+" requires a "+disp(RC.mut)+" receiver, which cannot be obtained from a "+disp(l.rc())+" object.")
      .line("Hint: remove the implementation of method "+m+".")
      .ex(pkg,l).addSpan(at.inner);
  }
  public FearlessException methodTAr_gsArityError(Literal d,Call c, int expected){
    int got= c.targs().size(); assert got != expected;
    String expS= expected == 0 
      ? "no type arguments" 
      : expected+" type argument"+(expected == 1 ? "" : "s");
    String gotS= got == 0 
      ? "no type arguments" 
      : got+" type argument"+(got == 1 ? "" : "s");
    return withCallSpans(Err.of()
      .pCallCantBeSatisfied(d,c)
      .line("Wrong number of type arguments for "+methodSig(c.name())+".")
      .line("This method expects "+expS+", but this call provides "+gotS+".")
      .ex(pkg,c), c);
  }  
  public FearlessException methodReceiverNot_Rcc(Literal d, Call c, T recvType){
    String name= switch(recvType){
      case T.X x -> disp(x.name());
      case T.RCX(var _, var x) -> disp(x.name());
      case T.ReadImmX(var x) -> disp(x.name());
      case T.RCC _-> { throw Bug.unreachable(); }
    };
  return withCallSpans(Err.of()
    .pCallCantBeSatisfied(d,c)
    .line("The receiver is of type "+name+". This is a type parameter.")
    .line("Type parameters cannot be receivers of method calls.")
    .ex(pkg,c), c);
  }
  /*private String sig_ToStr(Sig s){
    var bsS= Join.of(s.bs(),"[",",","]","");
    var tsS= Join.of(s.ts(),"(",",",")","");
    return s.rc()+" "+s.m()+bsS+tsS+":"+s.ret()+";";
  }*/
  public FearlessException mCallFrame(M m, FearlessException fe){
    return fe.addFrame(methodSig(m.sig().m())+" line "+m.sig().span().inner.startLine(), m.sig().span().inner);
  }
  public interface IsSub{ boolean isSub(List<B> bs, T a, T b); }
  
  
  public FearlessException nameNot_Available(E.X x, T declared, Change why, List<B> bs){
    throw Bug.of();/*var d= new ArgDiag(x.name(), declared, Optional.empty(), Optional.empty(), why, Note.NONE, bs, List.of());
    return Err.of()
      .line("The parameter "+disp(x.name())+" is not available here.")
      .blank()
      .pArgDiag(d)
      .ex(pkg,x)
      .addSpan(x.span().inner);*/
  }
}