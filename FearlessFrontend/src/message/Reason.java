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

public final class Reason{
  final Supplier<E> footerE;
  final String info;//package-private: only message.* should read it
  final Set<String> printed;
  String info(Set<String> sink){ sink.addAll(printed); return info; }
  public final T best;//exposed, seen by the type system
  private Reason(T best, String info, Set<String> printed, Supplier<E> footerE){
    this.best= best; this.info= info; this.printed= printed; this.footerE= footerE;
  }
  public boolean isEmpty(){ return info.isEmpty(); }
  public static Reason pass(T got){ return new Reason(got, "", Set.of(), () -> { throw Bug.unreachable(); }); }
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
    if (!explRC){ return new Reason(got, base(es, ts, blame, bs, got, expected), es.printed(), () -> baseFooterE(ts.scope(), got, expected)); }
    return hintExplicitRC(es, ts, got, base(es, ts, blame, bs, got, expected), er, rc, blame);
  }
  private static String base(TypeSystemErrors es, TypeSystem ts, E blame, List<B> bs, T got, T expected){
    var skipImm= !ts.isSub(bs, got, expected.withRC(RC.imm));
    return "Object literal is of type "+es.err().expReprDirect(skipImm, blame)+" instead of a subtype of "+es.err().typeRepr(skipImm, expected)+".";
  }
  private static Reason hintExplicitRC(TypeSystemErrors es, TypeSystem ts, T got, String base, T.RCC expected, RC rc, E blame){
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
    return new Reason(got, e.text(), es.printed(), () -> baseFooterE(ts.scope(), got, expected));
  }
  private static E baseFooterE(TypeScope s, T actual, T req){ return TypeScope.bestInterestingScope(s, TypeScope.interestFromDeclVsReq(actual, req)).contextE(); }
  public static Reason callResultCannotHaveRequiredType(TypeSystem ts, Literal d, Call call, TRequirement req, List<T> got, Sig sig){
    var es= ts.reasonE();
    return new Reason(got.getFirst(), es.err().gotMsg(true, "Method call "+es.err().methodSig(call.rc().toStrSpace(), d, call.name()), got, req.t()), es.printed(),
      () -> baseFooterE(ts.scope(), sig.ret().withRC(RC.imm), req.t().withRC(RC.imm)));
  }
  public static Reason parameterDoesNotHaveRequiredTypeHere(
    TypeSystem ts, X x, TRequirement req, T declared, WithT cur, boolean declaredOkExpected
  ){
    var es= ts.reasonE();
    var got= cur.currentT();
    var rcOnly= rcOnlyMismatch(got, req.t());
    var base= es.err().gotMsg(!rcOnly, es.err().expRepr(x), List.of(got), req.t());
    var noDeclaredNote= !rcOnly || declared.equals(got);
    if (noDeclaredNote){ return new Reason(got, base, es.printed(), () -> baseFooterE(ts.scope(), got, req.t())); }
    var e= es.err().line(base);
    e.line(declaredOkExpected
      ? "Note: the declared type "+es.err().typeRepr(true, declared)+" would instead be a valid subtype."
      : "Note: the declared type "+es.err().typeRepr(true, declared)+" also does not satisfy the requirement."
    );
    var trace= vpaTrace(es, cur);
    if (!trace.isEmpty()){ e.line("Capture adaptation trace:\n"+trace+"."); }
    return new Reason(got, e.text(), es.printed(), () -> baseFooterE(ts.scope(), got, req.t()));
  }
  private static String vpaTrace(TypeSystemErrors es, WithT cur){ return switch (cur){
    case Same _ -> "";
    case KeepStrengthenToImm(_, var m, var to, var tail) -> traceKeep(es, tail, "strengthenToImm", to, m);
    case KeepSetToReadImm(_, var m, var to, var tail) -> traceKeep(es, tail, to.explicitRC().isPresent() ? "setToRead" : "setToReadImm", to, m);
  };}
  private static String traceKeep(TypeSystemErrors es, WithT tail, String op, T to, M m){
    var prev= vpaTrace(es, tail);
    if (tail.currentT().equals(to)){ return prev; }
    var edge= " --"+op+"(line "+m.sig().span().inner.startLine()+")--> "+es.err().typeRepr(true, to);
    if (prev.isEmpty()){ return es.err().typeRepr(true, tail.currentT())+edge; }
    return prev+edge;
  }
}