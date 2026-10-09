package message;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Map;
import java.util.function.Consumer;

import core.*;
import core.E.*;
import core.T.C;
import utils.Bug;
import utils.Join;
import utils.Range;
import utils.Streams;

public class CompactPrinter{
  public CompactPrinter(String mainPkg, Map<String,String> uses, Consumer<String> printed, boolean trunk){ t= new TypeNamePrinter(trunk,mainPkg,uses,printed); }
  public String limit(E e,int limit){
    assert limit >= 0;
    var root= ofE(e);
    while (render(root).length() > limit){
      var k= new BestPicker().pick(root);
      if (!k.isCompactable()){ break; }
      k.compact();
    }
    return render(root);
  }
  private String render(PE root){
    sb.setLength(0);
    root.accString(this);
    return sb.toString();
  }
  StringBuilder sb= new StringBuilder();
  TypeNamePrinter t;
  public String msgT(T t){
    ofT(t).accString(this);
    return sb.toString();
  }
  CompactPrinter append(String s){ sb.append(s); return this; }
  CompactPrinter append(RC rc){ sb.append(rc); return this; }
  String bounds(List<B> bs){ return Join.of(bs.stream().map(B::compactToString),"[",",","]",""); }
  public static final class Compactable{
    public static final Compactable no= new Compactable(false);
    boolean compacted; private Compactable(boolean can){ compacted= !can; }
    public static Compactable of(){ return new Compactable(true); }
    public boolean isCompactable(){ return !compacted; }
    public void compact(){ assert !compacted; compacted= true; }
  }
  interface Acc<XX>{ void acc(XX x,CompactPrinter sb); }
  static <XX> void wrap(CompactPrinter sb, String open, String close, List<XX> xs, String sep, Acc<XX> a){
    if (xs.isEmpty()){ return; }
    sb.append(open);
    for (int i : Range.of(xs)){
      if (i > 0){ sb.append(sep); }
      a.acc(xs.get(i),sb);
    }
    sb.append(close);
  }
  static boolean showTargs(RC rc, int nt){ return rc != RC.imm || nt != 0; }
  static void accTargs(CompactPrinter sb, RC rc, List<PT> targs){
    if (!showTargs(rc,targs.size())){ return; }
    sb.append("[").append(rc);
    wrap(sb,",","",targs,",",PN::accString);
    sb.append("]");
  }
  public sealed interface PN{
    default Compactable k(){ return Compactable.no; }
    void accString(CompactPrinter sb);
  }
  public sealed interface PE extends PN{}
  public sealed interface PT extends PN{}

  public record PX(String x) implements PE{
    public void accString(CompactPrinter sb){ sb.append(x); }
  }
  public record PTypeE(PT t) implements PE{
    public void accString(CompactPrinter sb){ t.accString(sb); }
  }
  public record PCall(PE recv, String m, RC rc, List<PT> targs, List<PE> args, Compactable k) implements PE{
    public void accString(CompactPrinter sb){
      Acc<PE> acc= k.isCompactable() ? PN::accString : (_,b)->b.append("-");
      acc.acc(recv,sb);
      sb.append(m);
      accTargs(sb,rc,targs);
      wrap(sb,"(",")",args,",",acc);
    }
  }
  public record PLit(RC rc, boolean priv, String name, List<PC> cs, String self, List<PM> ms, Compactable k) implements PE{
    public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      if (!priv){ sb.append(name); } else if (!cs.isEmpty()){ cs.getFirst().accString(sb); }
      if (!k.isCompactable()){ sb.append("{-}"); return; }
      if (!priv){ wrap(sb,"","",cs,",",PC::accString); }
      if (ms.isEmpty()){ sb.append("{}"); return; }
      var selfHidden= self.equals("this") || self.equals("_");
      var start= selfHidden ? "{" : "{'"+self+" ";
      wrap(sb,start,"}",ms,";",PN::accString);
    }
  }
  public record PTX(String x) implements PT{
    public void accString(CompactPrinter sb){ sb.append(x); }
  }
  public record PTRCC(RC rc, PC c) implements PT{
    public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      c.accString(sb);
    }
  }
  public record PC(String name, List<PT> ts, Compactable k) implements PN{
    public void accString(CompactPrinter sb){
      sb.append(name);
      wrap(sb,"[","]",ts,",",k.isCompactable()?PN::accString:(_,b)->b.append("-"));
    }
  }
  public record PM(RC rc, String m, String bs, List<String> xs, List<PT> ts, PT ret, Optional<PE> body, Compactable k) implements PN{
    public void accString(CompactPrinter sb){
      if (!k.isCompactable()){ accCompactedMeth(sb); return; }
      sb.append(rc.toStrSpace());
      sb.append(m);
      sb.append(bs);
      wrap(sb,"(",")",Streams.zip(xs,ts).<Consumer<CompactPrinter>>map((x,t)->b->param(b,x,t)).toList(),",",Consumer::accept);
      sb.append(":");
      ret.accString(sb);
      body.ifPresent(e->{ sb.append("->"); e.accString(sb); });
    }
    private static void param(CompactPrinter b, String x, PT t){
      if (!x.equals("_")){ b.append(x).append(":"); }
      t.accString(b);
    }
    private void accCompactedMeth(CompactPrinter sb){
      if (body.isEmpty()){ sb.append(m); wrap(sb,"(",")",xs,",",(_,b)->b.append("-")); return; }
      wrap(sb,"(",")->",xs,",",(_,b)->b.append("-"));
      body.get().accString(sb);
    }
  }
  public PE ofE(E e){ return switch (e){
    case X(var name, var src) -> new PX(src.inner instanceof fearlessFullGrammar.E.Implicit?"::": name);
    case Type(var type, _) -> new PTypeE(ofT(type));
    case Call c -> ofCall(c);
    case Literal l -> ofLit(l);
  };}
  PE ofCall(Call c){
    var targs= ofTs(c.targs());
    var args= ofEs(c.es());
    return new PCall(ofE(c.e()), c.name().s(), c.rc(), targs, args, Compactable.of());
  }
  PE ofLit(Literal l){
    var ms= l.ms().stream().filter(m->m.sig().origin().equals(l.name())).map(m->ofM(m.sig(), m.xs(), m.e().map(this::ofE))).toList();
    var priv= l.infName();
    var name= priv ? ""
      : t.of(l.name()) + bounds(l.bs())+":"; // name[bs]:
    var onlyFirstC= priv && !l.cs().isEmpty();
    var cs= ofCs(l.src(),onlyFirstC ? List.of(l.cs().getFirst()) : l.cs());
    var top= l.thisName().equals("this");
    var rc= top ? RC.imm : l.rc();
    return new PLit(rc, priv, name, cs, l.thisName(), ms, Compactable.of());
  }
  List<PE> ofEs(List<E> es){ return es.stream().map(this::ofE).toList(); }
  List<PT> ofTs(List<T> ts){ return ts.stream().map(this::ofT).toList(); }
  PT ofT(T t){ return switch (t){
    case T.X(var name, _) -> new PTX(name);
    case T.RCX(var rc, var x) -> new PTX(rc+" "+x.name());
    case T.ReadImmX(var x) -> new PTX("read/imm "+x.name());
    case T.RCC(var rc, var c, _) -> new PTRCC(rc, ofC(c));
  };}
  PC ofC(T.C c){
    return new PC(t.of(c.name()), ofTs(c.ts()), c.ts().isEmpty() ? Compactable.no : Compactable.of());
  }
  List<PC> ofCs(Src src,List<T.C> cs){
    List<fearlessFullGrammar.T.C> oCs= switch (src.inner){
      case fearlessFullGrammar.Declaration(_, _, var decCs, _)->decCs;
      case fearlessFullGrammar.E.TypedLiteral(var rcc, _, _)->List.of(rcc.c());
      case fearlessFullGrammar.E.Literal _->List.of();
      default -> throw Bug.of(src.inner.getClass().getSimpleName());
    };
    var original= oCs.stream().map(c->c.name()).toList();
    return cs.stream()
      .filter(c->original.isEmpty() || original.contains(c.name()) || original.contains(c.name().withoutPkgName()))
      .map(this::ofC)
      .toList();
  }
  PM ofM(Sig s, List<String> xs, Optional<PE> body){
    var bs= bounds(s.bs());
    return new PM(s.rc(), s.m().s(), bs, xs, ofTs(s.ts()), ofT(s.ret()), body, Compactable.of());
  }
  public String sig(Sig s){
    var pm= ofM(s, Collections.nCopies(s.m().arity(),"_"),Optional.empty());
    assert sb.isEmpty();
    sb.append(" ".repeat(6-s.rc().toStrSpace().length()));//line up
    pm.accString(this);
    return sb.toString();
  }
}