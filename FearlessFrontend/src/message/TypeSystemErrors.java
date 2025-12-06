package message;

import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import metaParser.Message;
import metaParser.NameSuggester;
import typeSystem.ArgMatrix;
import typeSystem.TypeSystem.*;
import typeSystem.ArgMatrix.*;
import utils.Bug;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;

import java.util.List;
import java.util.stream.Collectors;

import core.*;
import core.E.*;

public final class TypeSystemErrors {
  private TypeSystemErrors(){}
 
  public static FearlessException overrideMismatch(Sig sub, Sig sup, String reason){
    return Code.TypeError.of( 
      "Invalid override for method " + sub.m().s() + ".\n"
      + "Method in " + sub.origin().s() + " conflicts with method in " + sup.origin().s() + ".\n"
      + "Reason: " + reason
    ).addSpan(sub.span().inner);
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
    var needed= promos.stream().map(MType::rc).distinct().sorted().toList();
    var promoLines= promos.stream()
      .map(m->"  - "+m.promotion()+": needs receiver "+m.rc())
      .collect(Collectors.joining("\n"));    
    String msg=
      "Receiver capability mismatch for call " + Message.displayString(c.name().s()) + ".\n"
    + "The receiver (the object on which the method is called) has capability: " + recvRc + ".\n"
    +  Join.of(needed,"The generated promotions for this call require the receiver to be ", " or ", ".\n")
    + "Available method promotions:\n" + promoLines + "\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), c.name().s().length()));
    //TODO: yes, we should just make so that the pos of a call is the start of the method name!
  }
  public static FearlessException callableMethodAbstract(TSpan at, M got, RC receiver){
    var s= got.sig();
    var msg=
      "Abstract method is being called.\n"
      + "Receiver capability at call site: "+receiver+".\n"
      + "Method: "+s.m().s()+".\n"
      + "Declared abstract in: "+s.origin().s()+".\n";
    return Code.TypeError.of(msg).addSpan(at.inner);
  }
  public static FearlessException methodHopelessArg(Call c, int argi, List<TRequirement> reqs, List<TResult> res){
    var msg=//TODO: even, consider difference for base (no promotion) or alternatives
      "Call of method "+Message.displayString(c.name().s())+" can not be satisfied.\n"
    + "Argument "+argi+" has incompatible type: MISSING INFO"+".\n"
    + "Argument type was required to be one of .... in order to call promotion...\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), 100));
  }
  public static FearlessException methodNotDeclared(Call c, Literal d){
    String name= c.name().s();
    var candidates= d.ms().stream().map(M::sig).toList();
    var sameName= candidates.stream().filter(s->s.m().s().equals(name)).toList();    
    if (sameName.isEmpty()){
      var names= candidates.stream().map(s->s.m().s()).distinct().sorted().toList();
      return Code.TypeError.of(
         NameSuggester.suggest(name, names, (_, cs, best) -> {
           StringBuilder sb= new StringBuilder()
             .append("Call of method ").append(Message.displayString(name))
             .append(".\nSuch method is not declared on type ")
             .append(Message.displayString(d.name().s())).append(".\n");
           best.ifPresent(b->sb.append("Did you mean ").append(Message.displayString(b)).append(" ?\n"));
           if (cs.isEmpty()){ sb.append("The type ").append(Message.displayString(d.name().s())).append(" does not have any methods.\n"); }
           else {
             sb.append("Available methods:\n");
             for (String n : cs){ candidates.stream()
               .filter(s -> s.m().s().equals(n))
               .forEach(s -> sb.append("  ").append(sigToStr(s)).append("\n"));
             }
           }
           return sb.toString();
         })
      ).addSpan(Parser.span(c.pos(), name.length()));
    }
    var sameArity= sameName.stream().filter(s->s.m().arity() == c.es().size()).toList();
    if (sameArity.isEmpty()){
       String avail= Join.of(sameName.stream().map(s->Integer.toString(s.m().arity())).distinct().sorted(), "", " or ", "");
       String msg= "Method " + Message.displayString(name) + " declared on type " + Message.displayString(d.name().s())
       + " but with different parameter count.\n"
       + "Call supplies " + c.es().size() 
       + " arguments, but available overloads take " + avail + ".\n";
       return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), name.length()));
    }    
    String availRc= Join.of(sameArity.stream().map(s->s.rc().toString()).distinct().sorted(), "", " and ", "");
    String msg= "Method " + Message.displayString(name) + " declared on type " + Message.displayString(d.name().s())
    + " exists, but not with the requested capability.\n"
    + "Call requires the existence of a "+ Message.displayString(c.rc().toString()) + " method.\n"
    + "Available capabilities for this method: " + availRc + ".\n";
    return Code.TypeError.of(msg).addSpan(Parser.span(c.pos(), name.length()));
  }  
  public static FearlessException typeError(Pos at, List<TResult> got, List<TRequirement> req){ throw Bug.todo(); }
  public static FearlessException uncallableMethodDeadCode(TSpan at, M got, RC receiver){ throw Bug.todo(); }  
  public static FearlessException methodTArgsArityError(Call c){ throw Bug.todo(); }
  public static FearlessException methodArgsDisagree(Call c, ArgMatrix mat){ throw Bug.todo(); }
  public static FearlessException methodReceiverNotRcc(Call c, T recvType){ throw Bug.todo(); }
  
  public static String sigToStr(Sig s){
    var bsS= Join.of(s.bs(),"[",",","]","");
    var tsS= Join.of(s.ts(),"(",",",")","");
    var rcS= s.rc().toString()+" ";      
    var mS= s.m().toString();
    return rcS+mS+bsS+tsS+":"+s.ret()+";";
  }
  public static FearlessException mCallFrame(M m, FearlessException fe) {
    return fe.addFrame("the body of method "+Message.displayString(m.sig().m().s()), m.sig().span().inner);
  }
}