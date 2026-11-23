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
  final boolean showImm;
  private Reason(T best, boolean showImm, String info, Set<String> printed, Supplier<E> footerE){
    this.best= best; this.showImm= showImm; this.info= info; this.printed= printed; this.footerE= footerE;
  }
  public boolean isEmpty(){ return info.isEmpty(); }
  public static Reason pass(T got){ return new Reason(got, false, "", Set.of(), () -> { throw Bug.unreachable(); }); }
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
    var e= es.err().line("Object literal has type "+es.err().expReprDirect(!show, blame)+" instead of a subtype of "+es.err().typeRepr(!show, expected)+".");
    if (explRC){ e.line(explicitRC(es, blame, rc, er.rc())); }
    return new Reason(got, show, e.text(), es.printed(), () -> baseFooterE(ts.scope(), got, expected));
  }
  private static String explicitRC(TypeSystemErrors es, E blame, RC rc, RC required){
    E blameOk= switch (blame){
      case Literal l -> l.withRC(rc);
      case Type(var t, var src) -> new Type(t.withRC(rc), src);
      default -> throw Bug.unreachable();
    };
    var why= rc == required ? "." : " (needed to satisfy the "+disp(required)+" requirement).";
    return "Write "+es.err().expReprDirect(false, blameOk)+" if you need "+(rc == RC.iso ? "an " : "a ")+disp(rc)+" object literal"+why;
  }
  private static E baseFooterE(TypeScope s, T actual, T req){ return TypeScope.bestInterestingScope(s, TypeScope.interestFromDeclVsReq(actual, req)).contextE(); }
  public static Reason callResultCannotHaveRequiredType(TypeSystem ts, List<B> bs, Literal d, Call call, TRequirement req, List<T> got, Sig sig){
    var es= ts.reasonE();
    var show= got.stream().anyMatch(g -> onlyRC(ts, bs, g, req.t()));
    return new Reason(got.getFirst(), show, es.err().gotMsg(!show, "Method call "+es.err().methodSig(call.rc().toStrSpace(), d, call.name()), got, req.t()), es.printed(),
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
    if (noDeclaredNote){ return new Reason(got, show, base, es.printed(), () -> baseFooterE(ts.scope(), got, req.t())); }
    var e= es.err().line(base);
    var self= TypeSystemErrors.isSelfName(ts.scope(), x.name());
    if (!self){ e.line(declaredOkExpected
      ? "Note: the declared type "+es.err().typeRepr(true, declared)+" would instead be a valid subtype."
      : "Note: the declared type "+es.err().typeRepr(true, declared)+" also does not satisfy the requirement."
    ); }
    e.line(adaptation(es, self, x, cur));
    return new Reason(got, show, e.text(), es.printed(), () -> baseFooterE(ts.scope(), got, req.t()));
  }
  static String adaptation(TypeSystemErrors es, boolean self, X x, WithT cur){
    return (self ? "The capability of the methods changes the type of " : "Capturing changes the type of ")+es.err().expRepr(x)+":"+steps(es, cur)
      +"\nCapture adaptation trace:\n"+vpaTrace(es, cur)+".";
  }
  private static String steps(TypeSystemErrors es, WithT cur){
    if (!(cur instanceof Keep k)){ return ""; }
    var s= k.m().sig();
    return steps(es, k.tail())+"\n- "+es.err().typeRepr(false, k.tail().currentT())+" becomes "+es.err().typeRepr(false, k.currentT())
      +" inside the "+disp(s.rc())+" method "+methodSig(s.m())+" (line "+s.span().inner.startLine()+").";
  }
  private static String vpaTrace(TypeSystemErrors es, WithT cur){
    if (!(cur instanceof Keep k)){ return es.err().typeRepr(false, cur.currentT()); }
    var op= k instanceof KeepStrengthenToImm ? "strengthenToImm" : k.currentT().explicitRC().isPresent() ? "setToRead" : "setToReadImm";
    return vpaTrace(es, k.tail())+" --"+op+"(line "+k.m().sig().span().inner.startLine()+")--> "+es.err().typeRepr(false, k.currentT());
  }
}