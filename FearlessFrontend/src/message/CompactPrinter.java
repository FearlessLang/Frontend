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
import utils.Push;
import utils.Range;
import utils.Streams;

public final class CompactPrinter{
  public CompactPrinter(String mainPkg, Map<String,String> uses, Consumer<String> printed){ t= new TypeNamePrinter(mainPkg, uses, printed); }
  public String limit(E e, E focus, int limit){
    assert limit >= 0;
    onPath(e, focus);
    var root= ofE(e);
    var len= render(root).length();
    while (len > limit){
      var k= new BestPicker().pick(root);
      if (!k.isCompactable()){ break; }
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
  private boolean onPath(E e, E focus){
    var res= e == focus || switch (e){
      case X _, Type _ -> false;
      case Call c -> Push.of(c.e(), c.es()).stream().anyMatch(ei -> onPath(ei, focus));
      case Literal l -> l.ms().stream().anyMatch(m -> m.e().filter(ei -> onPath(ei, focus)).isPresent());
    };
    if (res){ path.add(e); }
    return res;
  }
  private Compactable k(Optional<E> e){ return Compactable.of(e.filter(path::contains).isPresent()); }
  StringBuilder sb= new StringBuilder();
  TypeNamePrinter t;
  public String msgT(T t){
    ofT(t).accString(this);
    return sb.toString();
  }
  CompactPrinter append(String s){ sb.append(s); return this; }
  CompactPrinter omit(){ omitted= true; return append("..."); }
  String bounds(List<B> bs){ return Join.of(bs.stream().map(b -> b.rcs().equals(EnumSet.of(RC.imm)) ? b.x() : b.compactToString()), "[", ",", "]", ""); }
  public static final class Compactable{
    public static final Compactable no= new Compactable(false, false);
    boolean compacted; boolean pinned; private Compactable(boolean can, boolean pinned){ compacted= !can; this.pinned= pinned; }
    public static Compactable of(boolean pinned){ return new Compactable(true, pinned); }
    public boolean isCompactable(){ return !compacted; }
    public void compact(){ assert !compacted && !pinned; compacted = true; }
    void keep(){ assert compacted; compacted = false; pinned = true; }
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
  static boolean showTargs(RC rc, int nt){ return rc != RC.imm || nt != 0; }
  static void accTargs(CompactPrinter sb, RC rc, List<PT> targs){
    if (!showTargs(rc, targs.size())){ return; }
    sb.append("["+rc);
    wrap(sb, ",", "", targs, ",", PN::accString);
    sb.append("]");
  }
  public sealed interface PN{
    default Compactable k(){ return Compactable.no; }
    void accString(CompactPrinter sb);
  }
  public sealed interface PE extends PN{}
  public sealed interface PT extends PN{}

  public record PX(String x) implements PE{
    @Override public void accString(CompactPrinter sb){ sb.append(x); }
  }
  public record PTypeE(PT t) implements PE{
    @Override public void accString(CompactPrinter sb){ t.accString(sb); }
  }
  public record PCall(PE recv, String m, RC rc, List<PT> targs, List<PE> args, Compactable k) implements PE{
    boolean infix(){ return args.size() == 1 && !m.startsWith(".") && !m.equals("#"); }
    @Override public void accString(CompactPrinter sb){
      Acc<PE> acc= k.isCompactable() ? PN::accString : (_,b) -> b.omit();
      accGrouped(sb, acc, recv, k.isCompactable() ? recv instanceof PCall c && c.infix() : !infix());
      sb.append(infix() ? " "+m : m);
      accTargs(sb, rc, targs);
      if (!infix()){ wrap(sb, "(", ")", args, ",", acc); return; }
      sb.append(" ");
      accGrouped(sb, acc, args.getFirst(), k.isCompactable() && args.getFirst() instanceof PCall);
    }
    private void accGrouped(CompactPrinter sb, Acc<PE> acc, PE e, boolean group){
      wrap(sb, group ? "(" : "", group ? ")" : "", List.of(e), "", acc);
    }
  }
  public record PLit(RC rc, boolean priv, String name, List<PC> cs, String self, List<PM> ms, Compactable k) implements PE{
    @Override public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      if (!priv){ sb.append(name); }
      else if (!cs.isEmpty()){ cs.getFirst().accString(sb); }
      if (!k.isCompactable()){ sb.append("{").omit().append("}"); return; }
      if (!priv){ wrap(sb, "", "", cs, ",", PC::accString); }
      if (ms.isEmpty()){ sb.append("{}"); return; }
      var selfHidden= self.equals("this") || self.equals("_");
      var start= selfHidden ? "{" : "{'"+self+" ";
      wrap(sb, start, "}", ms, ";", PN::accString);
    }
  }
  public record PTX(String x) implements PT{
    @Override public void accString(CompactPrinter sb){ sb.append(x); }
  }
  public record PTRCC(RC rc, PC c) implements PT{
    @Override public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      c.accString(sb);
    }
  }
  public record PC(String name, List<PT> ts, Compactable k) implements PN{
    @Override public void accString(CompactPrinter sb){
      sb.append(name);
      wrap(sb, "[", "]", ts, ",", k.isCompactable() ? PN::accString : (_,b) -> b.omit());
    }
  }
  public record PM(RC rc, String m, String bs, List<String> xs, List<PT> ts, PT ret, Optional<PE> body, Compactable k) implements PN{
    @Override public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace()).append(m).append(bs);
      wrap(sb, "(", ")", Streams.zip(xs, ts).<Consumer<CompactPrinter>>map((x,t) -> b -> param(b, x, t)).toList(), ",", Consumer::accept);
      sb.append(":");
      ret.accString(sb);
      body.ifPresent(e -> accBody(sb, e));
    }
    private void accBody(CompactPrinter sb, PE e){
      sb.append("->");
      if (!k.isCompactable()){ sb.omit(); return; }
      e.accString(sb);
    }
    private static void param(CompactPrinter b, String x, PT t){
      if (!x.equals("_") && !x.equals("::")){ b.append(x).append(":"); }
      t.accString(b);
    }
  }
  public PE ofE(E e){ return switch (e){
    case X(var name, var src) -> ofX(name, src);
    case Type(var type, _) -> new PTypeE(ofT(type));
    case Call c -> ofCall(c);
    case Literal l -> ofLit(l);
  };}
  private final Set<String> implicits= new HashSet<>();
  PE ofX(String name, Src src){
    if (!(src.inner instanceof fearlessFullGrammar.E.Implicit)){ return new PX(name); }
    implicits.add(name);
    return new PX("::");
  }
  PE ofCall(Call c){
    var targs= ofTs(c.targs());
    var args= ofEs(c.es());
    return new PCall(ofE(c.e()), c.name().s(), c.rc(), targs, args, k(Optional.of(c)));
  }
  PE ofLit(Literal l){
    var ms= l.ms().stream().filter(m -> m.sig().origin().equals(l.name())).map(m -> ofM(m.sig(), m.xs(), m.names(), m.e())).toList();
    var priv= l.infName();
    var name= priv ? ""
      : t.of(l.name())+bounds(l.bs())+":"; // name[bs]:
    var onlyFirstC= priv && !l.cs().isEmpty();
    var cs= ofCs(l.src(), onlyFirstC ? List.of(l.cs().getFirst()) : l.cs());
    var top= l.thisName().equals("this");
    var rc= top ? RC.imm : l.rc();
    return new PLit(rc, priv, name, cs, l.thisName(), ms, k(Optional.of(l)));
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
    return new PC(t.of(c.name()), ofTs(c.ts()), c.ts().isEmpty() ? Compactable.no : Compactable.of(false));
  }
  List<PC> ofCs(Src src, List<T.C> cs){
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
  PM ofM(Sig s, List<String> xs, List<String> names, Optional<E> body){
    var e= body.map(this::ofE);
    var implicit= xs.stream().anyMatch(implicits::contains);
    return new PM(s.rc(), s.m().s(), bounds(s.bs()), implicit ? List.of("::") : names, ofTs(s.ts()), ofT(s.ret()), e, k(body));
  }
  public String sig(Sig s){
    var xs= Collections.nCopies(s.m().arity(), "_");
    var pm= ofM(s, xs, xs, Optional.empty());
    assert sb.isEmpty();
    sb.append(" ".repeat(6-s.rc().toStrSpace().length()));//line up
    pm.accString(this);
    return sb.toString();
  }
  public String sig(M m){
    ofM(m.sig(), m.xs(), m.names(), Optional.empty()).accString(this);
    return sb.toString();
  }
}