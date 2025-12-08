package message;

import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import fearlessFullGrammar.MName;
import metaParser.Message;
import typeSystem.ArgMatrix.*;
import typeSystem.TypeSystem.*;

final class Err{
  final StringBuilder sb= new StringBuilder();
  static Err of(){ return new Err(); }
  static String disp(Object o){ return Message.displayString(o.toString()); }
  String text(){ return sb.toString().stripTrailing(); }
  FearlessException ex(){ return Code.TypeError.of(text()); }
  Err line(String s){
    s= s.stripTrailing();
    sb.append(s).append(s.isEmpty() ? "" : "\n");
    return this;
  }
  Err blank(){
    int n= sb.length();
    if (n == 0){ return this; }
    if (n >= 2 && sb.charAt(n-1) == '\n' && sb.charAt(n-2) == '\n'){ return this; }
    if (sb.charAt(n-1) != '\n'){ sb.append('\n'); }
    sb.append('\n');
    return this;
  }
  Err lineIf(String s){ return s.isEmpty() ? this: line(s); }
  Err blockIf(String s){
    s= s.stripTrailing();
    sb.append(s);
    return this;
  }
  Err pArgsDisagreeIntro(){ return line("Each argument is compatible with at least one promotion, but no single promotion works for all arguments."); }
  Err pAcceptedByPromos(int argi, List<String> promos){ return line("  - argument "+(argi+1)+Join.of(promos," is compatible with promotions: ",", ",".")); }
  Err pReceiverPromotionFailures(List<MType> promos){
    pPromotionFailuresHdr();
    for (var m:promos){
      line("  - receiver fails for promotion "+m.promotion()+":");
      pFailCause("Needs receiver "+disp(m.rc())+".");
    }
    return this;
  }
  Err pFailCause(String s){
    s= s.stripTrailing();
    if (s.isEmpty()){ return this; }
    sb.append(indent(s,"    ")).append('\n');
    return this;
  }
  Err conflictsWithMethodIn(Sig sup){ return line("Conflicts with method in "+disp(sup.origin().s())+"."); }
  Err pCallCantBeSatisfied(Call c){
    return line("This call to method "+methodSig(c.name())+" does not type-check.");
  }
  Err pMethodContext(String kind, Sig s, String where){
    line(kind+" for method "+methodSig(s.m())+".");
    return lineIf(where.isEmpty() ? "" : "In "+disp(where)+".");
  }
  Err pArgIncompatibleAllPromos(int argi){
    return line(argLabel(argi)+" is incompatible with all available promotions.");
  }
  Err pArgHasType(int argi, List<T> gotTs){
    return line(argLabel(argi)+" has type "+dispTypes(gotTs)+".");
  }
  Err pPromotionFailuresHdr(){ return blank().line("Promotion failures:"); }
  Err pPromoFail(int argi, String promo){ return line("  - argument "+(argi+1)+" fails for promotion "+promo+":"); }
  Err pExpected(T expected){ return line("    Expected: "+disp(expected)+"."); }
  Err pArgDiag(TypeSystemErrors.ArgDiag d){ return
     blank()
    .pArgDiagHeader(d)
    .pArgDiagNote(d)
    .pArgDiagWhy(d);
  }
  Err pHopelessArg(Call c, int argi, List<TRequirement> reqs, List<TResult> res, Optional<TypeSystemErrors.ArgDiag> diag){
    pCallCantBeSatisfied(c).pArgIncompatibleAllPromos(argi);
    diag.ifPresentOrElse(this::pArgDiag, ()->pArgHasType(argi, res.stream().map(TResult::best).distinct().toList()));
    pPromotionFailuresHdr();
    IntStream.range(0,reqs.size()).forEach(i->pHopelessArgFail(argi, reqs.get(i), res.get(i), diag));
    return this;
  }
  private Err pHopelessArgFail(int argi, TRequirement req, TResult tr, Optional<TypeSystemErrors.ArgDiag> diag){
    pPromoFail(argi, req.reqName());
    if (diag.isEmpty()){ return pExpected(req.t()).pFailCause(tr.reason()); }
    var got= diag.get().got().get();//Offensive
    return pFailCause(disp(got)+" is not a subtype of "+disp(req.t())+".");
  }
  private Err pArgDiagHeader(TypeSystemErrors.ArgDiag d){
    String par= "The parameter "+disp(d.x());
    String dd= disp(d.declared());
    if (d.got().isEmpty()){ return line(par+" has declared type "+dd+"."); }
    String hasType= " here has type "+disp(d.got().get());
    String declPart= " (declared as type "+dd+")";
    if (d.expected().isEmpty()){
      if (d.declared().equals(d.got().get())){ return line(par+hasType+"."); }
      return line(par+declPart+hasType+".");
    }
    String end= ", that is not a subtype of "+disp(d.expected().get())+".";
    if (d.declared().equals(d.got().get())){ return line(par+hasType+end); }
    return line(par+declPart+hasType+end);
  }
  private Err pArgDiagNote(TypeSystemErrors.ArgDiag d){
    String dd= disp(d.declared());
    String ee= d.expected().map(Err::disp).orElse("the expected type");
    String note= switch(d.note()){
      case NONE -> "";
      case DECLARED_OK_SOME_CALL_EXPECTED -> Join.of(d.fitsPromos(),"Note: the declared type "+dd+" would work for: ",", ",".");
      case DECLARED_OK_THIS_EXPECTED -> "Note: the declared type "+dd+" is a subtype of "+ee+".";
      case DECLARED_NOT_OK_THIS_EXPECTED -> "Note: the declared type "+dd+" is also not a subtype of "+ee+".";
    };
    return lineIf(note);
  }
  private Err pArgDiagWhy(TypeSystemErrors.ArgDiag d){
    T expected= d.expected().orElse(d.declared());
    String w= d.why().render(d.x(), expected, d.got(), d.declared(), d.bs());
    return blockIf(w);
  }
  Err lineGotMsg(T got, T expected){ return line(gotMsg(got, expected)); }
  static String methodSig(MName m){ return methodSig("",m); }
  static String methodSig(String pre, MName m){
    return disp(Join.of(
      IntStream.range(0,m.arity()).mapToObj(_->"_"),
      pre+m.s()+"(",",",")",
      pre+m.s()
    ));
  }
  private String argLabel(int argi){ return "Argument "+(argi+1); }
  private String indent(String s, String pre){ return pre+s.replace("\n","\n"+pre); }
  private String gotMsg(T got, T expected){
    return disp(got)+" is not a subtype of "+disp(expected)+".";
  }
  private String dispTypes(List<T> ts){
    var ss= ts.stream().map(Err::disp).distinct().sorted().toList();
    if (ss.size() == 1){ return ss.getFirst(); }
    return Join.of(ss,""," or ","");
  }
}