package message;

import java.util.List;
import java.util.Optional;
import java.util.Map;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import core.T.C;
import utils.Bug;
import utils.Join;

public class CompactPrinter{
  public CompactPrinter(String mainPkg, Map<String,String> uses, boolean trunk){ t= new TypeNamePrinter(trunk,mainPkg,uses); }
  public String limit(E e,int limit){
    assert limit >= 0;
    PE root= ofE(e);
    while (root.size() > limit){
      var k= new BestPicker().pick(root);
      if (!k.isCompactable()){ break; }
      k.compact();
    }
    assert sb.isEmpty();
    root.accString(this);
    assert sb.length() == root.size();
    return sb.toString();
  }
  StringBuilder sb= new StringBuilder();
  TypeNamePrinter t;
  String tNameToStr(TName n){ return t.of(n); }
  String msgTName(TName n){ return t.ofFull(n); }
  String msgT(T t){     
    var pt= ofT(t);
    pt.accString(this);
    return sb.toString();
  }
  CompactPrinter append(String s){ sb.append(s); return this; }
  CompactPrinter append(RC rc){ sb.append(rc); return this; }
  String bounds(List<B> bs){ return Join.of(bs.stream().map(B::compactToString),"[",",","]",""); }
  public static final class Compactable{
    public static final Compactable NO= new Compactable(false);
    boolean compacted; private Compactable(boolean can){ compacted = !can; }
    public static Compactable of(){ return new Compactable(true); }
    public boolean isCompactable(){ return !compacted; }
    public void compact(){ assert !compacted; compacted= true; }
  }
  interface ToInt<XX>{ int of(XX x); }//Can not use X since E.X is imported
  static <XX> int sum(List<XX> xs, ToInt<XX> f){ return xs.stream().mapToInt(f::of).sum(); }
  static int seps(int n){ return n <= 1 ? 0 : n - 1; }
  static <XX> int wrapLen(List<XX> xs,int openClose,ToInt<XX> itemLen){
    return xs.isEmpty() ? 0 : openClose + seps(xs.size()) + sum(xs,itemLen);
  }
  interface Acc<XX>{ void acc(XX x,CompactPrinter sb); }
  static <XX> void wrap(CompactPrinter sb, String open, String close, List<XX> xs, String sep, Acc<XX> a){
    if (xs.isEmpty()){ return; }
    sb.append(open);
    for (int i= 0; i < xs.size(); i++){
      if (i > 0){ sb.append(sep); }
      a.acc(xs.get(i),sb);
    }
    sb.append(close);
  }
  static int rcPrefixLen(RC rc){ return rc == RC.imm ? 0 : rc.toString().length() + 1; }
  static boolean showTargs(RC rc, int nt){ return rc != RC.imm || nt != 0; }
  static int targsPunctLen(RC rc, int nt){
    if (!showTargs(rc,nt)){ return 0; }
    if (nt == 0){ return 2 + rc.toString().length(); }//[]
    return 3 + rc.toString().length() + seps(nt);//[,]
  }
  static int argsPunctLen(int na){ return na == 0 ? 0 : 2 + seps(na); } //()
  static int callLen(String m, RC rc, int nt, int na){
    return m.length() + targsPunctLen(rc,nt) + argsPunctLen(na);
  }
  //static boolean privateLike(TName n){ return n.simpleName().startsWith("_"); }
  static int xsWithColonsLen(List<String> xs){
    return sum(xs, x-> x.equals("_")? 0: x.length() + 1);
  } // nothing if x is _ it will be printed as just the type, or "x:"
  static void accTargs(CompactPrinter sb, RC rc, List<PT> targs){
    if (!showTargs(rc,targs.size())){ return; }
    if (targs.isEmpty()){sb.append("[").append(rc).append("]"); return; }
    wrap(sb,"["+rc+",","]",targs,",",PN::accString);
  }
  public sealed interface PN{
    default Compactable k(){ return Compactable.NO; }
    void accString(CompactPrinter sb);
  }
  public sealed interface PE extends PN{ int size(); }
  public sealed interface PT extends PN{ int size(); }

  public record PX(String x) implements PE{
    public int size(){ return x.length(); }
    public void accString(CompactPrinter sb){ sb.append(x); }
  }
  public record PTypeE(PT t) implements PE{
    public int size(){ return t.size(); }
    public void accString(CompactPrinter sb){ t.accString(sb); }
  }
  public record PCall(PE recv, String m, RC rc, List<PT> targs, List<PE> args, Compactable k, int length) implements PE{
    public int size(){
      int s= length + sum(targs, PT::size);
      if (k.isCompactable()){ return s + recv.size() + sum(args, PE::size); }
      return s + 1 + args.size(); // "-" receiver + one "-" per hidden arg
    }
    public void accString(CompactPrinter sb){
      if (k.isCompactable()){ recv.accString(sb); }
      else { sb.append("-"); }
      sb.append(m);
      accTargs(sb,rc,targs);
      wrap(sb,"(",")",args,",",k.isCompactable()?PN::accString:(_,b)->b.append("-"));
    }
  }
  public record PLit(RC rc, boolean priv, String name, List<PC> cs, String self, List<PM> ms, Compactable k, int length) implements PE{
    public int size(){
      if (k.isCompactable()){ return length + wrapLen(cs,0,PC::size) + sum(ms, PM::size); }
      if (!priv){ return rcPrefixLen(rc) + name.length() + 3; }            // name already has ":"; then "{-}"
      int c0= cs.isEmpty()? 0 : cs.getFirst().size();
      return rcPrefixLen(rc) + c0 + 3;                                     // Bar{-} or {-}
    }
    public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      if (!k.isCompactable()){ accName(sb); sb.append("{-}"); return; }
      accName(sb);   
      if (!priv){ wrap(sb,"","",cs,",",PC::accString); }  
      if (ms.isEmpty()){ sb.append("{}"); return; }
      var start= (self.equals("this") || self.equals("_")) ? "{" : "{'"+self+" ";
      wrap(sb,start,"}",ms,";",PN::accString);
    }
  private void accName(CompactPrinter sb){
      if (!priv){ sb.append(name); return; }
      if (!cs.isEmpty()){ cs.getFirst().accString(sb); }
    }
  }
  public record PTX(String x) implements PT{
    public int size(){ return x.length(); }
    public void accString(CompactPrinter sb){ sb.append(x); }
  }
  public record PTRCC(RC rc, PC c) implements PT{
    public int size(){ return rcPrefixLen(rc) + c.size(); }
    public void accString(CompactPrinter sb){
      sb.append(rc.toStrSpace());
      c.accString(sb);
    }
  }
  public record PC(String name, List<PT> ts, Compactable k) implements PN{
    public int size(){
      int s= name.length();
      if (ts.isEmpty()){ return s; }
      s += 2 + seps(ts.size()); // [ , ]
      if (k.isCompactable()){ return s + sum(ts, PT::size); }
      return s + ts.size(); // one "-" per hidden arg
    }
    public void accString(CompactPrinter sb){
      sb.append(name);
      wrap(sb,"[","]",ts,",",k.isCompactable()?PN::accString:(_,b)->b.append("-"));
    }
  }
  public record PM(RC rc, String m, String bs, List<String> xs, List<PT> ts, PT ret, Optional<PE> body, Compactable k, int length) implements PN{
    public int size(){
      if (k.isCompactable()){
        int s= length + sum(ts, PT::size) + ret.size();
        return body.isEmpty() ? s : s + body.get().size();
      }
      if (body.isPresent()){
        if (xs.isEmpty()){ return body.get().size(); }
        return 4 + seps(xs.size()) + xs.size() + body.get().size(); // (-s)->e
      }
      if (xs.isEmpty()){ return m.length(); }
      return m.length() + 2 + seps(xs.size()) + xs.size(); // m(-s)
    }
    public void accString(CompactPrinter sb){
      if (!k.isCompactable()){ accCompactedMeth(sb); return; }
      sb.append(rc.toStrSpace());
      sb.append(m);
      sb.append(bs);
      wrap(sb,"(",")",IntStream.range(0,xs.size()).boxed().toList(),",",(i,b)->{
        String x= xs.get(i);
        if (!x.equals("_")){ b.append(x).append(":"); }
        ts.get(i).accString(b);
        });
      sb.append(":");
      ret.accString(sb);
      body.ifPresent(e->{ sb.append("->"); e.accString(sb); });
    }
    private void accCompactedMeth(CompactPrinter sb) {
      if (body.isEmpty()){ sb.append(m); wrap(sb,"(",")",xs,",",(_,b)->b.append("-")); return; }
      if (xs.isEmpty()){ body.get().accString(sb); return; }
      wrap(sb,"(",")",xs,",",(_,b)->b.append("-"));
      sb.append("->");
      body.get().accString(sb);
    }
  }
  public PE ofE(E e){ return switch(e){
    case X x -> new PX(x.src().inner instanceof fearlessFullGrammar.E.Implicit?"::": x.name());
    case Type t -> new PTypeE(ofT(t.type()));
    case Call c -> ofCall(c);
    case Literal l -> ofLit(l);
  };}
  PE ofCall(Call c){
    var targs= ofTs(c.targs());
    var args= ofEs(c.es());
    return new PCall(ofE(c.e()), c.name().s(), c.rc(), targs, args, Compactable.of(),
      callLen(c.name().s(), c.rc(), targs.size(), args.size()));
  }
  PE ofLit(Literal l){
    var ms= ofMs(l.name(),l.ms());
    boolean priv= l.infName();
    var name= priv ? ""
      : tNameToStr(l.name()) + bounds(l.bs())+":"; // name[bs]:
    var cs= ofCs(l.src(),priv && !l.cs().isEmpty() ? List.of(l.cs().getFirst()):l.cs());
    var top= l.thisName().equals("this");
    int s= rcPrefixLen(top?RC.imm:l.rc()) + 2 + seps(ms.size()) + name.length(); // {} and ";"
    var addSelf= !ms.isEmpty() && !top && !l.thisName().equals("_");
    if (addSelf){ s += 2 + l.thisName().length(); } // "'x "    
    return new PLit(top?RC.imm:l.rc(), priv, name, cs, l.thisName(), ms, Compactable.of(), s);
  }  
  List<PE> ofEs(List<E> es){ return es.stream().map(this::ofE).toList(); }
  List<PT> ofTs(List<T> ts){ return ts.stream().map(this::ofT).toList(); }
  PT ofT(T t){ return switch(t){
    case T.X x -> new PTX(x.name());
    case T.RCX x -> new PTX(x.rc()+" "+x.x().name());
    case T.ReadImmX x -> new PTX("read/imm "+x.x().name());
    case T.RCC r -> new PTRCC(r.rc(), ofC(r.c()));
  };}
  PC ofC(T.C c){
    return new PC(tNameToStr(c.name()), ofTs(c.ts()), c.ts().isEmpty() ? Compactable.NO : Compactable.of());
  }
  List<PC> ofCs(Src src,List<T.C> cs){
    List<fearlessFullGrammar.T.C> oCs= switch(src.inner){
      case fearlessFullGrammar.E.DeclarationLiteral d->d.dec().cs();
      case fearlessFullGrammar.Declaration d->d.cs();
      case fearlessFullGrammar.E.TypedLiteral d->List.of(d.t().c());
      case fearlessFullGrammar.E.Literal _->List.of();
      default -> throw Bug.of(src.inner.getClass().getSimpleName());
    };
    var original= oCs.stream().map(c->c.name()).toList();
    return cs.stream()
      .filter(c->extracted(c,original))
      .map(this::ofC)
      .toList();
  }
  private boolean extracted(C c, List<TName> original) {
    return original.isEmpty()
      || original.contains(c.name())
      || original.contains(c.name().withoutPkgName());
  }
  PM ofM(M m){
    var s= m.sig();
    Optional<PE> body= m.e().map(this::ofE);
    var ts= ofTs(s.ts());
    var ret= ofT(s.ret());
    var bs= bounds(s.bs());
    var len= mLen(s.rc(), s.m().s(), bs, m.xs(), body.isPresent());
    return new PM(s.rc(), s.m().s(), bs, m.xs(), ts, ret, body, Compactable.of(), len);
  }
  int mLen(RC rc, String m, String bs, List<String> xs, boolean hasBody){
    int s= rcPrefixLen(rc) + m.length() + bs.length();
    s += xs.isEmpty() ? 1 : 3 + seps(xs.size()) + xsWithColonsLen(xs);
    return hasBody ? s + 2 : s;
  }
  List<PM> ofMs(TName origin, List<M> ms){
    return ms.stream()
      .filter(m->m.sig().origin().equals(origin))
      .map(this::ofM)
      .toList();
  }
  public String sig(Sig s){
    var xs= IntStream.range(0,s.m().arity()).mapToObj(_->"_").toList();
    var ts= ofTs(s.ts());
    var ret= ofT(s.ret());
    var bs= bounds(s.bs());
    var pm= new PM(s.rc(), s.m().s(), bs, xs, ts, ret,
      Optional.empty(), Compactable.of(),
      mLen(s.rc(), s.m().s(), bs, xs, false));
    assert sb.isEmpty();
    if (s.rc() == RC.imm){ sb.append("      "); }//line up
    else {
      var l= s.rc().toString().length()+1;
      assert l <= 6:s.rc();//amount of space used
      sb.append(" ".repeat(6-l));
    }
    pm.accString(this);
    return sb.toString();
  }
}