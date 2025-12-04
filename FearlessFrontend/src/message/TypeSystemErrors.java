package message;

import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import metaParser.Message;
import typeSystem.ArgMatrix;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix.*;
import utils.Bug;
import core.T;
import fearlessFullGrammar.TName;

import java.util.List;
import java.util.stream.Collectors;

import core.E;
import core.E.Call;
import core.M;
import core.Sig;

public final class TypeSystemErrors {
  private TypeSystemErrors(){}
 
  public static FearlessException overrideMismatch(Sig sub, Sig sup, String reason){
    return Code.TypeError.of( 
      "Invalid override for method " + sub.m().s() + ".\n"
      + "Method in " + sub.origin().s() + " conflicts with method in " + sup.origin().s() + ".\n"
      + "Reason: " + reason
    ).addSpan(Parser.span(sub.pos(), 100));
  }
  public static FearlessException unresolvedConflict(TName type, M m1, M m2){
    return Code.TypeError.of(
      "Unresolved multiple inheritance conflict in type " + type.s() + ".\n"
      + "Method " + m1.sig().m().s() + " is inherited from both " 
      + m1.sig().origin().s() + " and " + m2.sig().origin().s() + ".\n"
      + "You must override this method explicitly to resolve the ambiguity."
    ).addSpan(Parser.span(type.pos(), type.s().length()));
  }
  public static FearlessException notKinded(T t){
    Pos p= getPos(t);//TODO: still a bad error, we will need to somehow pass more parameters in
    return Code.TypeError.of("Type "+t+" is not well-kinded.\nIt violates reference capability constraints.")
      .addSpan(Parser.span(p,1));
  }  
  private static Pos getPos(T t){
    if (t instanceof T.RCC rcc){ return rcc.c().name().pos(); }
    return Pos.UNKNOWN;//TODO: do we need to track pos around for the others too?
  }
  public static FearlessException notAffine(String name, List<E.X> usages){
    var msg= "Usage violation for parameter "+Message.displayString(name)+".\n"
      + "An iso parameter must be either:\n"
      + "- Captured in object literals.\n"
      + "- Directly used at most once.\n";
    var ex= Code.TypeError.of(msg);
    for (var x : usages){//Note: this does work via internal span expansion.
      ex.addSpan(Parser.span(x.pos(), x.name().length()));
    }
    return ex;
  }
  public static String makeErrResult(ArgMatrix mat, List<Integer> okProm, TRequirement req){
    return "Return requirement not met. Needed: " + req.t()+".\n Promotions: "+promos(mat,okProm);
  }
  private static String promos(ArgMatrix mat, List<Integer> idxs){
    return idxs.stream().map(i->mat.candidate(i).promotion()).sorted().collect(Collectors.joining(", "));
  }
  public static FearlessException methodReceiverRcBlocksCall(Call c, RC recvRc, List<MType> promos){
    var needRcs= Join.of(promos.stream().map(MType::rc).distinct()
      .sorted((a,b)->Integer.compare(a.ordinal(),b.ordinal())),"",", ","");
    var promoLines= promos.stream()
      .map(m->"  - "+m.promotion()+": needs receiver "+m.rc())
      .collect(Collectors.joining("\n"));
    var msg=
      "Receiver capability mismatch for call "+c.name().s()+".\n"
    + "Receiver capability: "+recvRc+".\n"
    + "No promotion is callable from "+recvRc+".\n"
    + "Promotions require receiver in: "+needRcs+".\n"
    + "Promotions checked:\n"+promoLines+"\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), 100));
  }
  public static FearlessException callableMethodAbstract(Pos at, M got, RC receiver){
    var s= got.sig();
    var msg=
      "Abstract method is being called.\n"
      + "Receiver capability at call site: "+receiver+".\n"
      + "Method: "+s.m().s()+".\n"
      + "Declared abstract in: "+s.origin().s()+".\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(at, 100));
  }
  public static FearlessException methodHopelessArg(Call c, int argi, List<TRequirement> reqs, List<TResult> res){
    var msg=//TODO: even, consider difference for base (no promotion) or alternatives
      "Call of method "+Message.displayString(c.name().s())+" can not be satisfied.\n"
    + "Argument "+argi+" has incompatible type: MISSING INFO"+".\n"
    + "Argument type was required to be one of .... in order to call promotion...\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), 100));
  }
  public static FearlessException methodNotDeclared(Call c, TName onType){
    var msg= "Call of method "+Message.displayString(c.name().s())
    + " but method not declared on type "
    + Message.displayString(onType.s()) + ".\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), 100));
  }
  public static FearlessException typeError(Pos at, List<TResult> got, List<TRequirement> req){ throw Bug.todo(); }
  public static FearlessException uncallableMethodDeadCode(Pos at, M got, RC receiver){ throw Bug.todo(); }  
  public static FearlessException methodTArgsArityError(Call c){ throw Bug.todo(); }
  public static FearlessException methodArgsDisagree(Call c, ArgMatrix mat){ throw Bug.todo(); }
  public static FearlessException methodReceiverNotRcc(Call c, T recvType){ throw Bug.todo(); }
}