package message;

import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

import core.*;
import core.E.*;
import fearlessParser.RC;
import typeSystem.ArgMatrix;
import typeSystem.TypeScope;
import typeSystem.Change.*;
import typeSystem.TypeSystem.TRequirement;
import utils.Bug;

import static message.Err.*;

public final class Reason{
  final Supplier<Optional<E>> footerE;
  final String info;//package-private: only message.* should read it
  public final T best;//exposed, seen by the type system
  private Reason(T best,String info, Supplier<Optional<E>> footerE){
    this.best=best; this.info= info; this.footerE= footerE;
  }
  public boolean isEmpty(){ return info.isEmpty(); }
  public static Reason pass(T got){ return new Reason(got,"",Optional::empty); }
  public static Reason literalDoesNotHaveRequiredType(
    E blame, List<B> bs, T got, T expected
    ){
    String base= Err.gotMsg(Err.expRepr(blame),got, expected);
    if (!(expected instanceof T.RCC er) || er.rc() == fearlessParser.RC.imm){
      return new Reason(got, base, Optional::empty);
    }
    String tn= bestNameHintExplicitRC(blame);
    if (tn.isEmpty()){ return new Reason(got, base, Optional::empty); }
    return hintExplicitRC(got, base, er,tn);
  }
  private static String bestNameHintExplicitRC(E e){ return switch(e){
    case Literal l-> l.rc() != RC.imm ? "" : bestNameDirect(l)+(l.infName()?"{...}":":{...}");
    case Type t ->  t.type().rc() != RC.imm ? "" : bestNameDirect(t);
    default ->{ throw Bug.unreachable(); }
  };}
  private static Reason hintExplicitRC(T got, String base, T.RCC er, String tn){
    var e= Err.of()
      .line(base)
      .line("Hint: write "+disp(er.rc()+" "+tn)
      +" if you need a "+disp(er.rc())+" object literal.");
    return new Reason(got, e.text(), Optional::empty);
  }
  public static Reason callResultCannotHaveRequiredType(
    Literal d, Call call, List<B> bs, ArgMatrix mat, List<Integer> okProm, TRequirement req, T got, Sig sig, TypeScope scope
  ){    
    assert !okProm.isEmpty();
    Supplier<Optional<E>> footerE= ()->{
      T decl0= sig.ret().withRC(fearlessParser.RC.imm);
      T req0= req.t().withRC(fearlessParser.RC.imm);
      List<T> interest= TypeScope.interestFromDeclVsReq(decl0, req0);
      var best= TypeScope.bestInterestingScope(scope, interest);
      return Optional.of(best.contextE());
    };
    return new Reason(got,gotMsg("Method call "+methodSig(d,call.name()),got, req.t()),
      footerE);
  }
  public static Reason parameterDoesNotHaveRequiredTypeHere(
    X x, List<B> bs, TRequirement req, T declared, WithT cur, boolean declaredOkExpected
  ){
    T got= cur.currentT();
    String base= Err.gotMsg(Err.expRepr(x), got, req.t());
    if (!Err.rcOnlyMismatch(got, req.t())){ return new Reason(got, base,Optional::empty); }
    var e= Err.of().line(base);
    if (declared.equals(got)){ return new Reason(got, base, Optional::empty); }
    e.line(declaredOkExpected
      ? "Note: the declared type "+disp(declared)+" would instead be a valid subtype."
      : "Note: the declared type "+disp(declared)+" also does not satisfy the requirement."
    );
    String trace= vpaTrace(cur);
    if (!trace.isEmpty()){ e.line("Capture adaptation trace:\n"+trace+"."); }
    return new Reason(got, e.text(),Optional::empty);
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
    if (from.equals(to)){ return prev; }
    String edge= " --"+op+"("+where(l,m)+")--> "+disp(to);
    if (prev.isEmpty()){ return disp(from)+edge; }
    return prev+edge;
  }
  private static String where(Literal l, M m){
    return "line "+m.sig().span().inner.startLine();
  }
}