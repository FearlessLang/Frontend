package message;

import java.util.List;

import core.*;
import core.E.*;
import typeSystem.ArgMatrix;
import typeSystem.Change.*;
import typeSystem.TypeSystem.TRequirement;
import static message.Err.*;

public final class Reason{
  final String promNames;
  final String info;//package-private: only message.* should read it
  public final T best;//exposed, seen by the type system
  private Reason(T best,String promNames,String info){//private: factories only
    this.best=best; this.promNames=promNames; this.info= info;
  }
  public boolean isEmpty(){ return info.isEmpty(); }
  public static Reason pass(T got){ return new Reason(got,"",""); }
  public static Reason pass(String promNames,T got){ return new Reason(got,promNames,""); }
  public static Reason expressionDoesNotHaveRequiredType(
    E blame, List<B> bs, String promNames, T got, T expected
  ){
    return new Reason(got,promNames,Err.of().lineGotMsg(got, expected).text());
  }
  public static Reason parameterDoesNotHaveRequiredTypeHere(
    X x, List<B> bs, String promNames, T expected, T declared, WithT cur, boolean declaredOkExpected
  ){
    T got= cur.currentT();
    var e= Err.of();
    e.line("Parameter "+disp(x.name())+" does not meet the required type.");
    e.indented("Here it has type "+disp(got)+", but it must be a subtype of "+disp(expected)+".");
    if (!declared.equals(got)){
      e.indented("Declared type: "+disp(declared)+".");
      e.indented(declaredOkExpected
        ? "Note: the declared type would satisfy the requirement; the mismatch comes from viewpoint adaptation."
        : "Note: the declared type also does not satisfy the requirement."
      );
      String trace= vpaTrace(cur);
      if (!trace.isEmpty()){ e.indented("Viewpoint adaptation trace: "+trace+"."); }
    }
    return new Reason(got,promNames,e.text());
  }
  public static Reason callResultCannotHaveRequiredType(
    Call call, List<B> bs, ArgMatrix mat, List<Integer> okProm, TRequirement req, T got
  ){
    assert !okProm.isEmpty();
    var promos= okProm.stream().<String>map(i->mat.candidate(i).promotion()).distinct().sorted().toList();
    var e= Err.of();
    e.line("Call result does not meet the required type.");
    e.indented("It has type "+disp(got)+", but it must be a subtype of "+disp(req.t())+".");
    e.indented("Promotions that matched the arguments: "+Join.of(promos,""," / ","")+".");
    return new Reason(got,req.reqName(),e.text());
  }
  private static String vpaTrace(WithT cur){ return switch(cur){
    case Same _ -> "";
    case KeepStrengthenToImm k -> traceStrengthenToImm(k);
    case KeepSetToRead k -> traceSetToRead(k);
    case KeepSetToReadImm k -> traceSetToReadImm(k);
  };}
  private static String traceStrengthenToImm(KeepStrengthenToImm k){
    return traceKeep(k.tail(), "strengthenToImm", k.tail().currentT(), k.currentT(), k.l(), k.m());
  }
  private static String traceSetToRead(KeepSetToRead k){
    return traceKeep(k.tail(), "setToRead", k.tail().currentT(), k.currentT(), k.l(), k.m());
  }
  private static String traceSetToReadImm(KeepSetToReadImm k){
    return traceKeep(k.tail(), "setToReadImm", k.tail().currentT(), k.currentT(), k.l(), k.m());
  }
  private static String traceKeep(WithT tail, String op, T from, T to, Literal l, M m){
    String prev= vpaTrace(tail);
    if (from.equals(to)){ return prev; } // avoid A->A noise
    String step= disp(from)+" --"+op+"@"+where(l,m)+"--> "+disp(to);
    if (prev.isEmpty()){ return step; }
    return prev+"; "+step;
  }
  private static String where(Literal l, M m){
    // Placeholder-ish but exercises extraction of l+m right now.
    // Refine later (maybe show only lit name, or only method, etc.).
    return bestName(l)+"."+Err.methodSig(m.sig().m())+" line "+m.sig().span().inner.startLine();
  }
}