package message;

import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Optional;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import core.*;
import core.E.*;
import utils.Bug;
import utils.Join;
import utils.Range;
import utils.Streams;

public final class CompactPrinter{
  public CompactPrinter(String mainPkg, Map<String,String> uses, Consumer<String> printed){ t= new TypeNamePrinter(mainPkg, uses, printed); }
  String limit(E e, E focus){
    markPath(e, focus);
    var root= ofE(e);
    var len= render(root).length();
    while (len > 120){
      var k= new BestPicker().pick(root);
      if (k.pinned){ break; }
      k.compact();
      var shorter= render(root).length();
      if (shorter >= len){ k.keep(); continue; }
      len = shorter;
    }
    return render(root);
  }
  boolean omitted;
  private String render(PE root){
    sb.setLength(0);
    omitted= false;
    root.accString(this);
    return sb.toString();
  }
  final Set<E> path= Collections.newSetFromMap(new IdentityHashMap<>());
  private boolean markPath(E e, E focus){
    var res= e == focus || e.children().anyMatch(ei -> markPath(ei, focus));
    if (res){ path.add(e); }
    return res;
  }
  StringBuilder sb= new StringBuilder();
  TypeNamePrinter t;
  public String msgT(T t){
    ofT(t).accString(this);
    return sb.toString();
  }
  CompactPrinter append(String s){ sb.append(s); return this; }
  CompactPrinter omit(){ omitted= true; return append("..."); }
  String bounds(List<B> bs){ return Join.of(bs.stream().map(b -> b.rcs().equals(EnumSet.of(RC.imm)) ? b.x() : b.compactToString()), "[", ",", "]", ""); }
  static final class Compactable{
    static final Compactable no= new Compactable(true);
    boolean compacted; boolean pinned; Compactable(boolean pinned){ this.pinned= pinned; }
    void compact(){ assert !compacted && !pinned; compacted = true; }
    void keep(){ assert compacted; compacted = false; pinned = true; }
    <N extends PN> Acc<N> acc(){ return compacted ? (_,b) -> b.omit() : PN::accString; }
  }
  interface Acc<XX>{ void acc(XX x, CompactPrinter sb); }
  static <XX> void wrap(CompactPrinter sb, String open, String close, List<XX> xs, String sep, Acc<XX> a){
    if (xs.isEmpty()){ return; }
    sb.append(open);
    for (int i : Range.of(xs)){
      if (i > 0){ sb.append(sep); }
      a.acc(xs.get(i), sb);
    }
    sb.append(close);
  }
  sealed interface PN{
    default Compactable k(){ return Compactable.no; }
    void accString(CompactPrinter sb);
  }
  sealed interface PE extends PN{}
  sealed interface PT extends PN{}

  record PText(String s) implements PE, PT{
    @Override public void accString(CompactPrinter sb){ sb.append(s); }
  }
  record PTypeE(PT t) implements PE{
    @Override public void accString(CompactPrinter sb){ t.accString(sb); }
  }
  record PCall(PE recv, String m, RC rc, List<PT> targs, List<PE> args, Compactable k) implements PE{
    boolean infix(){ return args.size() == 1 && !m.startsWith(".") && !m.equals("#"); }
    @Override public void accString(CompactPrinter sb){
      Acc<PE> acc= k.acc();
      accGrouped(sb, acc, recv, k.compacted ? !infix() : recv instanceof PCall c && c.infix());
      sb.append(infix() ? " "+m : m);
      if (rc != RC.imm || !targs.isEmpty()){ sb.append("["+rc); wrap(sb, ",", "", targs, ",", PN::accString); sb.append("]"); }
      if (!infix()){ wrap(sb, "(", ")", args, ",", acc); return; }
      sb.append(" ");
      accGrouped(sb, acc, args.getFirst(), !k.compacted && args.getFirst() instanceof PCall);
    }
    private void accGrouped(CompactPrinter sb, Acc<PE> acc, PE e, boolean group){
      wrap(sb, group ? "(" : "", group ? ")" : "", List.of(e), "", acc);
    }
  }
  record PLit(RC rc, boolean priv, String name, List<PC> cs, String self, List<PM> ms, Compactable k) implements PE{
    boolean csShown(){ return priv || !k.compacted; }
    @Override public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace()).append(name);
      if (csShown()){ wrap(sb, "", "", cs, ",", PC::accString); }
      if (k.compacted){ sb.append("{").omit().append("}"); return; }
      if (ms.isEmpty()){ sb.append("{}"); return; }
      var selfHidden= self.equals("this") || self.equals("_");
      var start= selfHidden ? "{" : "{'"+self+" ";
      wrap(sb, start, "}", ms, ";", PN::accString);
    }
  }
  record PTRCC(RC rc, PC c) implements PT{
    @Override public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      c.accString(sb);
    }
  }
  record PC(String name, List<PT> ts, Compactable k) implements PN{
    @Override public void accString(CompactPrinter sb){
      sb.append(name);
      wrap(sb, "[", "]", ts, ",", k.acc());
    }
  }
  record PM(RC rc, String m, String bs, List<String> xs, List<PT> ts, PT ret, Optional<PE> body, Compactable k) implements PN{
    @Override public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace()).append(m).append(bs);
      wrap(sb, "(", ")", Streams.zip(xs, ts).<Consumer<CompactPrinter>>map((x,t) -> b -> param(b, x, t)).toList(), ",", Consumer::accept);
      sb.append(":");
      ret.accString(sb);
      wrap(sb, "->", "", body.stream().toList(), "", k.acc());
    }
    private static void param(CompactPrinter b, String x, PT t){
      if (!x.equals("_")){ b.append(x).append(":"); }
      t.accString(b);
    }
  }
  private PE ofE(E e){ return switch (e){
    case X(var name, var src) -> ofX(name, src);
    case Type(var type, _) -> new PTypeE(ofT(type));
    case Call c -> ofCall(c);
    case Literal l -> ofLit(l);
  };}
  private final Set<String> implicits= new HashSet<>();
  private PE ofX(String name, Src src){
    if (!(src.inner instanceof fearlessFullGrammar.E.Implicit)){ return new PText(name); }
    implicits.add(name);
    return new PText("::");
  }
  private PE ofCall(Call c){
    var targs= ofTs(c.targs());
    var args= c.es().stream().map(this::ofE).toList();
    return new PCall(ofE(c.e()), c.name().s(), c.rc(), targs, args, new Compactable(path.contains(c)));
  }
  private PE ofLit(Literal l){
    var ms= l.ms().stream().filter(m -> m.sig().origin().equals(l.name())).map(this::ofM).toList();
    var priv= l.infName();
    var name= priv ? ""
      : t.of(l.name())+bounds(l.bs())+":"; // name[bs]:
    var cs= ofCs(l.src(), priv ? l.cs().stream().limit(1).toList() : l.cs());
    var rc= l.thisName().equals("this") ? RC.imm : l.rc();
    return new PLit(rc, priv, name, cs, l.thisName(), ms, new Compactable(path.contains(l)));
  }
  private List<PT> ofTs(List<T> ts){ return ts.stream().map(this::ofT).toList(); }
  private PT ofT(T t){ return switch (t){
    case T.X(var name, _) -> new PText(name);
    case T.RCX(var rc, var x) -> new PText(rc+" "+x.name());
    case T.ReadImmX(var x) -> new PText("read/imm "+x.name());
    case T.RCC(var rc, var c, _) -> new PTRCC(rc, ofC(c));
  };}
  private PC ofC(T.C c){
    return new PC(t.of(c.name()), ofTs(c.ts()), new Compactable(c.ts().isEmpty()));
  }
  private List<PC> ofCs(Src src, List<T.C> cs){
    List<fearlessFullGrammar.T.C> oCs= switch (src.inner){
      case fearlessFullGrammar.Declaration(_, _, var decCs, _) -> decCs;
      case fearlessFullGrammar.E.TypedLiteral(var rcc, _, _) -> List.of(rcc.c());
      case fearlessFullGrammar.E.Literal _ -> List.of();
      default -> throw Bug.of(src.inner.getClass().getSimpleName());
    };
    var real= WellFormednessErrors.written(t.uses());
    var original= oCs.stream().map(c -> resolved(real, c.name())).toList();
    return cs.stream()
      .filter(c -> original.isEmpty() || original.contains(c.name()))
      .map(this::ofC)
      .toList();
  }
  private TName resolved(Map<String,String> real, TName n){
    var s= real.getOrDefault(n.s(), n.pkgName().isEmpty() ? t.mainPkg()+"."+n.s() : real.getOrDefault(n.pkgName(), n.pkgName())+"."+n.simpleName());
    return new TName(s, n.arity(), n.pos());
  }
  private PM ofM(M m){
    var e= m.e().map(this::ofE);
    var xs= m.xs().stream().anyMatch(implicits::contains) ? List.of("_") : m.names();
    var k= new Compactable(m.e().filter(path::contains).isPresent());
    var s= m.sig();
    return new PM(s.rc(), s.m().s(), bounds(s.bs()), xs, ofTs(s.ts()), ofT(s.ret()), e, k);
  }
  String sig(Sig s){
    assert sb.isEmpty();
    append(" ".repeat(6-s.rc().toStrSpace().length())).append(s.rc().toStrSpace()+s.m().s()+bounds(s.bs()));//line up
    wrap(this, "(", ")", ofTs(s.ts()), ", ", PN::accString);
    return append(": ").msgT(s.ret());
  }
}