package message;

import fearlessParser.Parser;
import fearlessParser.RC;
import files.Pos;
import metaParser.Message;
import metaParser.NameSuggester;
import typeSystem.ArgMatrix;
import typeSystem.TypeSystem.*;
import typeSystem.ViewPointAdaptation.*;
import typeSystem.ArgMatrix.*;
import utils.Bug;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

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
      .map(m->"  - "+m.promotion()+":\n      needs receiver "+m.rc())
      .collect(Collectors.joining("\n"));    
    String msg=
      "Receiver capability mismatch for call " + Message.displayString(c.name().s()) + ".\n"
    + "The receiver (the object on which the method is called) has capability: " + recvRc + ".\n"
    + Join.of(needed,"The generated promotions for this call require the receiver to be ", " or ", ".\n")
    + "Available method promotions:\n" + promoLines + "\n";
    return Code.TypeError.of(msg)
      .addSpan(Parser.span(c.pos(), c.name().s().length()))
      .addSpan(c.span().inner);//The two spans are the full range of the method call expression and the method name itself
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
    assert reqs.size() == res.size();
    String m= Message.displayString(c.name().s());
    var gotTs= res.stream().map(TResult::best).distinct().toList();
    String gotS= gotTs.size() == 1
      ? Message.displayString(gotTs.getFirst().toString())
      : Join.of(gotTs.stream().map(t->Message.displayString(t.toString())).distinct().sorted(),"", " or ", "");
    int i0= IntStream.range(0, reqs.size())
      .filter(i->"`As declared`".equals(reqs.get(i).reqName()))
      .findFirst().orElse(0);
    String diag= res.get(i0).reason();
    if (diag.isEmpty()){ diag= res.stream().map(TResult::reason).filter(s->!s.isEmpty()).findFirst().orElse(""); }
    var sb= new StringBuilder()
      .append("Call of method ").append(m).append(" can not be satisfied.\n")
      .append("Argument ").append(argi).append(" is incompatible with all available promotions.\n")
      .append("Argument ").append(argi).append(" has type ").append(gotS).append(".\n");
    if (!diag.isEmpty()){ sb.append(diag).append("\n"); }
    sb.append("\nPromotion failures:\n");
    IntStream.range(0, reqs.size()).forEach(i->sb
      .append("  - fails at argument ").append(argi).append(": ").append(reqs.get(i).reqName()).append("\n")
      .append("    Expected: ").append(Message.displayString(reqs.get(i).t().toString())).append(".\n"));
    return Code.TypeError.of(sb.toString())
      .addSpan(Parser.span(c.pos(), c.name().s().length()))
      .addSpan(c.es().get(argi).span().inner);
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
  public static FearlessException methodArgsDisagree(Call c, ArgMatrix mat){
    String m= Message.displayString(c.name().s());
    int ac= mat.aCount();
    int cc= mat.cCount();
    var sb= new StringBuilder()
      .append("Call of method ").append(m).append(" can not be satisfied.\n")
      .append("Each argument is compatible with some promotions, but no single promotion works for all arguments.\n")
      .append("Compatible promotions by argument:\n");
    IntStream.range(0,ac).forEach(argi->sb
      .append("  - argument ").append(argi)
      .append(" has type ").append(mat.res(argi,0).best()).append(": ")
      .append(Join.of(mat.okForArg(argi).stream()
        .map(ci->mat.candidate(ci).promotion())
        .distinct().sorted(),"",", ","\n")));
    sb.append("Promotion failures:\n");
    IntStream.range(0,cc).forEach(ci->{
      int argi= IntStream.range(0,ac).filter(a->!mat.res(a,ci).success()).findFirst().getAsInt();
      String reason= mat.res(argi,ci).reason();
      sb.append("  - fails at argument ").append(argi).append(": ")
        .append(mat.candidate(ci).promotion()).append("\n");
      if (!reason.isEmpty()){ sb.append(indent(reason,"    ")).append("\n"); }
    });
    return Code.TypeError.of(sb.toString())
      .addSpan(Parser.span(c.pos(), c.name().s().length()))
      .addSpan(c.span().inner);
  }
  private static String indent(String s, String pre){
    return pre+s.replace("\n","\n"+pre);
  }
  public static FearlessException method_ArgsDisagree(Call c, ArgMatrix mat){
    String m= Message.displayString(c.name().s());
    int ac= mat.aCount();
    int cc= mat.cCount();
    var sb= new StringBuilder()
      .append("Call of method ").append(m).append(" can not be satisfied.\n")
      .append("Each argument is compatible with some promotions, but no single promotion works for all arguments.\n")
      .append("Compatible promotions by argument:\n");
    IntStream.range(0,ac).forEach(argi->sb
      .append("  - argument ").append(argi)
      .append(" has type ").append(mat.res(argi,0).best()).append(": ")
      .append(Join.of(mat.okForArg(argi).stream()
        .map(ci->mat.candidate(ci).promotion())
        .distinct().sorted(),"",", ","\n")));
    sb.append("Promotion failures:\n");
    IntStream.range(0,cc)
      .forEach(ci->sb
        .append("  - ")
        .append(mat.candidate(ci).promotion())
        .append(IntStream.range(0, ac)
          .filter(argi->!mat.res(argi,ci).success())
          .mapToObj(argi->":\n      fails at argument "+argi+" ("+mat.res(argi,ci).reason()+")\n")
          .findFirst().get()));
    return Code.TypeError.of(sb.toString())
      .addSpan(Parser.span(c.pos(), c.name().s().length()))
      .addSpan(c.span().inner);
  }
  public static FearlessException typeError(E at, List<TResult> got, List<TRequirement> req){
    assert got.size() == req.size();
    var sb= new StringBuilder().append("Type mismatch.\n");
    for(int i= 0; i < got.size(); i++){
      var gi= got.get(i);
      if (gi.success()){ continue; }
      var ri= req.get(i);
      if (!ri.reqName().isEmpty()){
        sb.append("Requirement ").append(Message.displayString(ri.reqName())).append(".\n");
      }
      String reason= gi.reason();
      if (reason.startsWith("The parameter ")){ sb.append(reason).append("\n"); continue; }
      sb.append("Expected: ").append(ri.t()).append(".\n")
        .append("Got: ").append(gi.best()).append(".\n");
      if (!reason.isEmpty()){ sb.append("Reason: ").append(reason).append("\n"); }
    }
    return Code.TypeError.of(sb.toString()).addSpan(at.span().inner);
  }
  public static FearlessException uncallableMethodDeadCode(TSpan at, M got, RC receiver){ throw Bug.todo(); }  
  public static FearlessException methodTArgsArityError(Call c){ throw Bug.todo(); }
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
  public static FearlessException nameNotAvailable(E.X x, T declared, typeSystem.ViewPointAdaptation.Why why, List<B> bs){
    String xn= Message.displayString(x.name());
    var sb= new StringBuilder()
      .append("The parameter ").append(xn).append(" is not available in this scope.\n")
      .append("Declared type: ").append(declared).append(".\n");
    String w= why.render(x.name(),declared,Optional.empty(),declared,bs);
    if (!w.isEmpty()){ sb.append(w).append("\n"); }
    return Code.TypeError.of(sb.toString()).addSpan(x.span().inner);
  }
  public static String xHidden(String x, T expected, T declared, typeSystem.ViewPointAdaptation.Why why, boolean declaredOk, List<B> bs){
    String xn= Message.displayString(x);
    var sb= new StringBuilder()
      .append("The parameter ").append(xn).append(" is currently hidden.\n")
      .append("Expected type: ").append(expected).append(".\n")
      .append("Declared type: ").append(declared).append(".\n")
      .append(declaredOk
        ? "Note: the declared type would satisfy the expected type.\n"
        : "Note: the declared type would not satisfy the expected type.\n");
    String w= why.render(x,expected,Optional.empty(),declared,bs);
    if (!w.isEmpty()){ sb.append(w).append("\n"); }
    return sb.toString();
  }
  public static String gotMsg(T got, T expected){
    String g= Message.displayString(got.toString());
    String e= Message.displayString(expected.toString());
    return g+" is not a subtype of "+e+".";
  }
  public static String xMismatch(String x, T expected, T got, T declared, Why why, boolean declaredOk, List<B> bs){
    String xn= Message.displayString(x);
    String g= Message.displayString(got.toString());
    String e= Message.displayString(expected.toString());
    String w= why.render(x, expected, Optional.of(got), declared, bs);
    if (got.equals(declared) && w.isEmpty()){
      return "The parameter "+xn+" has type "+g+".\n"+g+" is not a subtype of "+e+".";
    }
    String d= Message.displayString(declared.toString());
    var sb= new StringBuilder().append("The parameter ").append(xn);
    if (!declared.equals(got)){ sb.append(" (declared as type ").append(d).append(") here has type ").append(g).append(".\n"); }
    else{ sb.append(" has type ").append(g).append(".\n"); }
    sb.append(g).append(" is not a subtype of ").append(e).append(".\n");
    if (declaredOk && !declared.equals(got) && !declared.equals(expected)){
      sb.append("Note: the declared type ").append(d).append(" is a subtype of ").append(e).append(".\n");
    }
    if (!w.isEmpty()){ sb.append(w).append("\n"); }
    return sb.toString();
  }
  public static Why discardWhy(T in, List<core.B> delta, RC rc0, boolean kindIsoImm){
    return (x,_,_,declared,_)->{
      String xn= Message.displayString(x);
      String td= Message.displayString(declared.toString());
      var base= "The parameter " + xn + " (declared as " + td + ")";
      var badScope= rc0 == RC.iso || rc0 == RC.imm;
      if (badScope){ return base+" is hidden because\nit is not visible from an " + rc0 + " scope."; }
      return base+" is hidden by viewpoint adaptation:\n (not well-kinded here).";//TODO: to improve when we understand better
    };
  }
  public static Why strengthenToImm(T in){
    return (x,expected,got,declared,bs)->"Viewpoint adaptation strengthened " + Message.displayString(x) + " to imm.";
  }
  public static Why setToRead(T in){ return (x,_,got,declared,_)->{//TODO: if it keeps not using in, it can become a method reference
    if (got.isEmpty()){ return ""; }
    String xn= Message.displayString(x);
    String g= Message.displayString(got.get().toString());
    String d= Message.displayString(declared.toString());
    return "Viewpoint adaptation set "+xn+" to "+g+" from "+d+" (the declared type).";
    };}
  public static Why useReadImm(T in){
    return (x,expected,got,declared,bs)->"Viewpoint adaptation replaced " + Message.displayString(x) + " with readImm(x).";
  }
  public static Why weakenedToRead(T in){
    return (x,expected,got,declared,bs)->"Viewpoint adaptation weakened " + Message.displayString(x) + " to read.";
  }
  public static Why filterFTVWhy(T in, List<B> bs0){
    var scope= bs0.stream().map(B::x).distinct().sorted().toList();
    var scopeSet= new HashSet<>(scope);
    var ftv= new HashSet<String>();
    addFtv(in, ftv);
    String missing= Join.of(ftv.stream().filter(x->!scopeSet.contains(x)).sorted(),"",", ","");
    String scopeS= Join.of(scope,"",", ","");
    return (x,expected,got,declared,bs)->{
      String xn= Message.displayString(x);
      String td= Message.displayString(declared.toString());
      return "The parameter " + xn + " (declared as " + td + ") is hidden because its type mentions type variable(s) ["
        + missing + "] which are not in scope here.\n"
        + "Type variables in scope: [" + scopeS + "].";
      };
    }
  private static void addFtv(T t, HashSet<String> out){
    switch(t){
      case T.X x -> out.add(x.name());
      case T.RCX(_, var x) -> out.add(x.name());
      case T.ReadImmX(var x) -> out.add(x.name());
      case T.RCC(_, var c) -> c.ts().forEach(ti->addFtv(ti,out));
    }
  }
}