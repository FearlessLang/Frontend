package message;

import java.util.List;
import java.util.function.Supplier;

import core.*;
import core.E.*;
import typeSystem.ArgMatrix;
import typeSystem.TypeScope;
import typeSystem.TypeSystem;
import typeSystem.Change.*;
import typeSystem.TypeSystem.TRequirement;
import utils.Bug;

import static message.Err.*;

public final class Reason{
  final Supplier<E> footerE;
  final String info;//package-private: only message.* should read it
  public final T best;//exposed, seen by the type system
  private Reason(T best,String info, Supplier<E> footerE){
    this.best=best; this.info= info; this.footerE= footerE;
  }
  public boolean isEmpty(){ return info.isEmpty(); }
  public static Reason pass(T got){ return new Reason(got,"",()->{throw Bug.unreachable();}); }
  public static Reason literalDoesNotHaveRequiredType(
    TypeSystem ts, E blame, List<B> bs, T got, T expected
    ){     
    if (!(expected instanceof T.RCC er) || er.rc() == core.RC.imm){
      return new Reason(got, base(ts,blame,bs,got,expected), ()->baseFooterE(ts.scope(),got,expected));
    }    
    boolean explRC= switch(blame){
      case Literal l->l.rc() != RC.imm;
      case Type(var t,_) ->  t.rc() != RC.imm;
      default ->{ throw Bug.unreachable(); }
    };
    if (!explRC){ return new Reason(got, base(ts,blame,bs,got,expected), ()->baseFooterE(ts.scope(),got,expected)); }
    return hintExplicitRC(ts,got, base(ts,blame,bs,got,expected), er,blame);
  }
  private static String base(TypeSystem ts, E blame, List<B> bs, T got, T expected){
    if (isInferErr(expected)){ return ts.err().gotMsgInferErr(ts.err().expRepr(blame),got);}
    var skipImm= !ts.isSub(bs, got, expected.withRC(RC.imm));
    return "Object literal is of type "+ts.err().expReprDirect(skipImm,blame)+" instead of a subtype of "+ts.err().typeRepr(skipImm,expected)+".";
  }
  private static Reason hintExplicitRC(TypeSystem ts,T got, String base, T.RCC expected, E blame){
    E blameOk=switch(blame){
      case Literal l->l.withRC(expected.rc());
      case Type(var t,var src) ->  new Type(t.withRC(expected.rc()),src);
      default ->{ throw Bug.unreachable(); }
    };  
    var e= ts.err()
      .line(base)
      .line("Hint: write "+ts.err().expReprDirect(false,blameOk)
      +" if you need a "+disp(expected.rc())+" object literal.");
    return new Reason(got, e.text(), ()->baseFooterE(ts.scope(),got,expected));
  }
  private static E baseFooterE(TypeScope s,T actual, T req){
    List<T> interest= TypeScope.interestFromDeclVsReq(actual, req);
    var best= TypeScope.bestInterestingScope(s, interest);
    return best.contextE();
  }
  public static Reason callResultCannotHaveRequiredType(
    TypeSystem ts, Literal d, Call call, List<B> bs, ArgMatrix mat, List<Integer> okProm, TRequirement req, T got, Sig sig, TypeScope scope
  ){    
    assert !okProm.isEmpty();
    Supplier<E> footerE= ()->{
      T decl0= sig.ret().withRC(core.RC.imm);
      T req0= req.t().withRC(core.RC.imm);
      List<T> interest= TypeScope.interestFromDeclVsReq(decl0, req0);
      var best= TypeScope.bestInterestingScope(scope, interest);
      return best.contextE();
    };
    return new Reason(got,ts.err().gotMsg(true,"Method call "+ts.err().methodSig(call.rc().toStrSpace(),d,call.name()),got, req.t()),
      footerE);
  }
  public static Reason parameterDoesNotHaveRequiredTypeHere(
    TypeSystem ts,X x, List<B> bs, TRequirement req, T declared, WithT cur, boolean declaredOkExpected
  ){
    T got= cur.currentT();
    var rcOnly= Err.rcOnlyMismatch(got, req.t());
    String base= ts.err().gotMsg(!rcOnly,ts.err().expRepr(x), got, req.t());
    if (!rcOnly){ return new Reason(got, base,()->baseFooterE(ts.scope(),got,req.t())); }
    var e= ts.err().line(base);
    if (declared.equals(got)){ return new Reason(got, base, ()->baseFooterE(ts.scope(),got,req.t())); }
    e.line(declaredOkExpected
      ? "Note: the declared type "+ts.err().typeRepr(true,declared)+" would instead be a valid subtype."
      : "Note: the declared type "+ts.err().typeRepr(true,declared)+" also does not satisfy the requirement."
    );
    String trace= vpaTrace(ts,cur);
    if (!trace.isEmpty()){ e.line("Capture adaptation trace:\n"+trace+"."); }
    return new Reason(got, e.text(),()->baseFooterE(ts.scope(),got,req.t()));
  }
  private static String vpaTrace(TypeSystem ts, WithT cur){ return switch(cur){
    case Same _ -> "";
    case KeepStrengthenToImm k -> traceStrengthenToImm(ts,k);
    case KeepSetToRead k -> traceSetToRead(ts,k);
    case KeepSetToReadImm k -> traceSetToReadImm(ts,k);
  };}
  private static String traceStrengthenToImm(TypeSystem ts, KeepStrengthenToImm k){
    return traceKeep(ts, k.tail(), "strengthenToImm", k.tail().currentT(), k.currentT(), k.l(), k.m());
  }
  private static String traceSetToRead(TypeSystem ts, KeepSetToRead k){
    return traceKeep(ts, k.tail(), "setToRead", k.tail().currentT(), k.currentT(), k.l(), k.m());
  }
  private static String traceSetToReadImm(TypeSystem ts, KeepSetToReadImm k){
    return traceKeep(ts, k.tail(), "setToReadImm", k.tail().currentT(), k.currentT(), k.l(), k.m());
  }
  private static String traceKeep(TypeSystem ts, WithT tail, String op, T from, T to, Literal l, M m){
    String prev= vpaTrace(ts,tail);
    if (from.equals(to)){ return prev; }
    String edge= " --"+op+"("+where(l,m)+")--> "+ts.err().typeRepr(true,to);
    if (prev.isEmpty()){ return ts.err().typeRepr(true,from)+edge; }
    return prev+edge;
  }
  private static String where(Literal l, M m){
    return "line "+m.sig().span().inner.startLine();
  }
}