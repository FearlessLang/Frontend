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
  public static Reason literalDoesNotHaveRequiredType(
    E blame, List<B> bs, String promNames, T got, T expected
  ){
    return new Reason(got,promNames,Err.gotMsg(Err.expRepr(blame),got, expected));
  }
  public static Reason callResultCannotHaveRequiredType(
    Call call, List<B> bs, ArgMatrix mat, List<Integer> okProm, TRequirement req, T got
  ){    
    assert !okProm.isEmpty();
    var promos= okProm.stream().<String>map(i->mat.candidate(i).promotion()).distinct().sorted().toList();
    return new Reason(got,
      "Promotions that matched the arguments: "+Join.of(promos,""," / ","")+".\n"
      +"Outer promotions: "+req.reqName()+".",
      Err.gotMsg(Err.expRepr(call),got, req.t()));
  }
  public static Reason parameterDoesNotHaveRequiredTypeHere(
    X x, List<B> bs, TRequirement req, T declared, WithT cur, boolean declaredOkExpected
  ){
    T got= cur.currentT();
    String base= Err.gotMsg(Err.expRepr(x), got, req.t());
    if (!Err.rcOnlyMismatch(got, req.t())){ return new Reason(got, req.reqName(), base); }
    var e= Err.of();
    e.line(base);
    e.line(declaredOkExpected
      ? "Note: the declared type "+disp(declared)+" would instead be a valid subtype."
      : "Note: the declared type "+disp(declared)+" also does not satisfy the requirement."
    );
    String trace= vpaTrace(cur);
    if (!trace.isEmpty()){ e.line("Capture adaptation trace:\n"+trace+"."); }
    return new Reason(got, req.reqName(), e.text());
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
    String edge= " --"+op+"("+where(l,m)+")--> "+disp(to);
    if (prev.isEmpty()){ return disp(from)+edge; }
    return prev+edge;
  }
  private static String where(Literal l, M m){
    return "line "+m.sig().span().inner.startLine();
    //return Err.methodSig(bestNamePgk(l),m.sig().m())+" line "+m.sig().span().inner.startLine();
  }
}