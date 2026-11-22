package message;

import static message.Err.*;

import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import core.*;
import core.E.*;
import typeSystem.TypeScope;
import typeSystem.TypeSystem;
import typeSystem.Change.*;
import typeSystem.TypeSystem.TRequirement;
import utils.Bug;
import utils.Push;

public final class Reason{
  final Supplier<E> footerE;
  final String info;//package-private: only message.* should read it
  final Set<String> printed;
  final List<T> stated;
  String info(Set<String> sink){ sink.addAll(printed); return info; }
  public final T best;//exposed, seen by the type system
  final boolean showImm;
  private Reason(T best, List<T> stated, boolean showImm, String info, Set<String> printed, Supplier<E> footerE){
    this.best= best; this.stated= stated; this.showImm= showImm; this.info= info; this.printed= printed; this.footerE= footerE;
  }
  public boolean isEmpty(){ return info.isEmpty(); }
  public static Reason pass(T got){ return new Reason(got, List.of(got), false, "", Set.of(), () -> { throw Bug.unreachable(); }); }
  private static boolean onlyRC(TypeSystem ts, List<B> bs, T got, T req){ return ts.isSub(bs, got.withRC(RC.imm), req.withRC(RC.imm)); }
  public static Reason literalDoesNotHaveRequiredType(
    TypeSystem ts, E blame, List<B> bs, T got, T expected
    ){
    var es= ts.reasonE();
    var er= (T.RCC)expected;
    var rc= er.rc() == RC.mutH ? RC.mut : er.rc();
    var explRC= rc != RC.imm && ts.isSub(bs, got.withRC(rc), er) && switch (blame){
      case Literal l -> l.rc() != RC.imm;
      case Type(var t, _) -> t.rc() != RC.imm;
      default -> throw Bug.unreachable();
    };
    var show= onlyRC(ts, bs, got, expected);
    var base= "Object literal is of type "+es.err().expReprDirect(!show, blame)+" instead of a subtype of "+es.err().typeRepr(!show, expected)+".";
    if (!explRC){ return new Reason(got, List.of(got, expected), show, base, es.printed(), () -> baseFooterE(ts.scope(), got, expected)); }
    return hintExplicitRC(es, ts, got, show, base, er, rc, blame);
  }
  private static Reason hintExplicitRC(TypeSystemErrors es, TypeSystem ts, T got, boolean show, String base, T.RCC expected, RC rc, E blame){
    E blameOk= switch (blame){
      case Literal l -> l.withRC(rc);
      case Type(var t, var src) -> new Type(t.withRC(rc), src);
      default -> throw Bug.unreachable();
    };
    var why= rc == expected.rc() ? "." : " (needed to satisfy the "+disp(expected.rc())+" requirement).";
    var e= es.err()
      .line(base)
      .line("Hint: write "+es.err().expReprDirect(false, blameOk)
      +" if you need "+(rc == RC.iso ? "an " : "a ")+disp(rc)+" object literal"+why);
    return new Reason(got, List.of(got, expected), show, e.text(), es.printed(), () -> baseFooterE(ts.scope(), got, expected));
  }
  private static E baseFooterE(TypeScope s, T actual, T req){ return TypeScope.bestInterestingScope(s, TypeScope.interestFromDeclVsReq(actual, req)).contextE(); }
  public static Reason callResultCannotHaveRequiredType(TypeSystem ts, List<B> bs, Literal d, Call call, TRequirement req, List<T> got, Sig sig){
    var es= ts.reasonE();
    var show= got.stream().anyMatch(g -> onlyRC(ts, bs, g, req.t()));
    return new Reason(got.getFirst(), Push.of(got, req.t()), show, es.err().gotMsg(!show, "Method call "+es.err().methodSig(call.rc().toStrSpace(), d, call.name()), got, req.t()), es.printed(),
      () -> baseFooterE(ts.scope(), sig.ret().withRC(RC.imm), req.t().withRC(RC.imm)));
  }
  public static Reason parameterDoesNotHaveRequiredTypeHere(
    TypeSystem ts, List<B> bs, X x, TRequirement req, T declared, WithT cur, boolean declaredOkExpected
  ){
    var es= ts.reasonE();
    var got= cur.currentT();
    var show= onlyRC(ts, bs, got, req.t());
    var base= es.err().gotMsg(!show, es.err().expRepr(x), List.of(got), req.t());
    var noDeclaredNote= !show || declared.equals(got);
    if (noDeclaredNote){ return new Reason(got, List.of(got, req.t()), show, base, es.printed(), () -> baseFooterE(ts.scope(), got, req.t())); }
    var e= es.err().line(base);
    var self= TypeSystemErrors.isSelfName(ts.scope(), x.name());
    if (!self){ e.line(declaredOkExpected
      ? "Note: the declared type "+es.err().typeRepr(true, declared)+" would instead be a valid subtype."
      : "Note: the declared type "+es.err().typeRepr(true, declared)+" also does not satisfy the requirement."
    ); }
    e.line(adaptation(es, self, x, cur));
    return new Reason(got, List.of(got, req.t(), declared), show, e.text(), es.printed(), () -> baseFooterE(ts.scope(), got, req.t()));
  }
  static String adaptation(TypeSystemErrors es, boolean self, X x, WithT cur){
    return (self ? "The capability of the methods changes the type of " : "Capturing changes the type of ")+es.err().expRepr(x)+":"+steps(es, cur)
      +"\nCapture adaptation trace:\n"+vpaTrace(es, cur)+".";
  }
  private static String steps(TypeSystemErrors es, WithT cur){ return switch (cur){
    case Same _ -> "";
    case KeepStrengthenToImm(_, var m, var to, var tail) -> step(es, tail, to, m);
    case KeepSetToReadImm(_, var m, var to, var tail) -> step(es, tail, to, m);
  };}
  private static String step(TypeSystemErrors es, WithT tail, T to, M m){
    var s= m.sig();
    return steps(es, tail)+"\n- "+es.err().typeRepr(false, tail.currentT())+" becomes "+es.err().typeRepr(false, to)
      +" inside the "+disp(s.rc())+" method "+es.err().methodSig(s.m())+" (line "+s.span().inner.startLine()+").";
  }
  private static String vpaTrace(TypeSystemErrors es, WithT cur){ return switch (cur){
    case Same(var t) -> es.err().typeRepr(false, t);
    case KeepStrengthenToImm(_, var m, var to, var tail) -> traceKeep(es, tail, "strengthenToImm", to, m);
    case KeepSetToReadImm(_, var m, var to, var tail) -> traceKeep(es, tail, to.explicitRC().isPresent() ? "setToRead" : "setToReadImm", to, m);
  };}
  private static String traceKeep(TypeSystemErrors es, WithT tail, String op, T to, M m){
    return vpaTrace(es, tail)+" --"+op+"(line "+m.sig().span().inner.startLine()+")--> "+es.err().typeRepr(false, to);
  }
}