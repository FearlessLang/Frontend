package message;

import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.IntStream;
import java.util.Locale;
import java.util.Optional;

import core.*;
import core.E.*;
import inject.TypeRename;
import metaParser.Message;
import metaParser.Span;
import typeSystem.Sources;
import utils.Bug;
import utils.Join;
import utils.Pos;
import utils.Push;
import utils.Streams;

public record Err(Function<T.C,T.C> publicHead, Function<TName,Literal> _decs, Function<Boolean,CompactPrinter> cpOf, Supplier<List<String>> notes, StringBuilder sb){
  CompactPrinter cp(){ return cpOf.apply(false); }
  public static String disp(Object o){ return Message.displayString(o.toString()); }
  static String funnel(String X, String owner, List<String> Xs){
    var x= disp(X);
    var dec= disp(owner);
    var declares= Xs.isEmpty() ? "none" : Join.of(Xs.stream().map(Err::disp), "", ", ", "", "");
    var funnelled= disp(Join.of(Push.of(Xs, X).stream().map(s -> s+":.."), owner+"[", ",", "]", ""));
    return "Generic type parameter "+x+" is not in scope inside the type declaration "+dec+".\n"
      +"A type declaration only sees the generic type parameters it declares itself;\nhere "+dec+" declares "+declares+".\n"
      +"Funnel "+x+" into "+dec+" by writing "+funnelled+", restating the bounds of "+x+".";
  }
  public static String genArity(int n){ return Join.of(Collections.nCopies(n, "_"), "[", ",", "]", ""); }
  static String staticTypeDecName(TName name){ return disp(name.simpleName()+genArity(name.arity())); }//for the parser and the well formedness errors only
  static <A> A redeclaredElement(List<A> es){
    return IntStream.range(0, es.size())
      .filter(i -> i != es.lastIndexOf(es.get(i)))
      .mapToObj(es::get)
      .findFirst().get();
  }

  String tNameA(TName n){ return cp().t.of(n)+genArity(n.arity()); }     // "A[_]"
  String tNameADisp(TName n){ return disp(tNameA(n)); }                      // displayString("A[_]")
  private boolean showInstanceOf(Literal l){ return l.infName() && !l.cs().isEmpty(); }
  private String bestLitName(Literal l){
    if (showInstanceOf(l)){ return typeReprRaw(true, new T.RCC(RC.imm, l.cs().getFirst(), l.span())); }
    if (anonLit(l)){ return anonRepr; }
    return tNameA(l.name());
  }
  private static TName bestName(inference.E.Literal l){
    if (!l.infName()){ return l.name(); }
    if (!l.cs().isEmpty()){ return l.cs().getFirst().name(); }
    return l.t() instanceof inference.IT.RCC r ? r.c().name() : l.name();
  }
  private boolean anonLit(Literal l){ return l.infName() && l.cs().isEmpty(); }
  private static final String anonRepr= "{...}";
  String anonOrInstanceOf(Literal l){ return anonLit(l) ? disp(anonRepr) : "object literal instance of "+disp(bestLitName(l)); }
  String theTypeOrObjectLiteral(Literal l){ return anonLit(l) ? "object literal "+disp(anonRepr) : "type "+disp(bestLitName(l)); }
  String typeRepr(inference.IT t){ return t.isTV() ? typeRepr(true, TypeRename.itToT(t)) : disp(typeReprRaw(t)); }
  String typeReprRaw(inference.IT t){ return typeReprRaw(t, Integer.MAX_VALUE); }
  String typeReprRaw(inference.IT t, int levels){ return switch (t){
    case inference.IT.RCC(var rc, var c, _) -> rc.map(RC::toStrSpace).orElse("")+cp().t.of(c.name())
      +(levels == 0 && !c.ts().isEmpty() ? "[...]" : Join.of(c.ts().stream().map(ti -> typeReprRaw(ti, levels-1)), "[", ",", "]", ""));
    case inference.IT.U _, inference.IT.Amb _ -> "?";
    default -> typeReprRaw(true, TypeRename.itToT(t));
  };}
  String typeRepr(boolean skipImm, T t){
    if (t instanceof T.RCC r && _anon(r.c().name()) instanceof Literal l){ return "the anonymous type of the object literal at "+at(l.span().inner); }
    return disp(typeReprRaw(skipImm, t));
  }
  private Literal _anon(TName n){
    var d= _decs.apply(n);
    if (d == null || !d.infName() || d.cs().stream().anyMatch(c -> !_decs.apply(c.name()).infName())){ return null; }
    return d;
  }
  static String at(Span s){ return "line "+s.startLine()+", column "+s.startCol(); }
  private String typeReprRaw(boolean skipImm, T t){
    var str= cp().msgT(showPublic(t));
    var noImmPrefix= skipImm || !(t instanceof T.RCC rcc && rcc.rc() == RC.imm);
    if (noImmPrefix){ return str; }
    return "imm "+str;
  }
  private T showPublic(T t){
    if (!(t instanceof T.RCC(var rc, var c, var span))){ return t; }
    var p= publicHead.apply(c);
    return new T.RCC(rc, p.withTs(p.ts().stream().map(this::showPublic).toList()), span);
  }
  static String count(int n, String noun){ return n+" "+noun+(n == 1 ? "" : "s"); }
  static String up(String s){ return s.substring(0, 1).toUpperCase(Locale.ROOT)+s.substring(1); }
  private Optional<Sig> own(TName n, Sig s){ return Sources.findCanonical(_decs.apply(n), s.m(), s.rc()); }
  private List<T.C> direct(List<T.C> cs){
    var indirect= cs.stream().flatMap(o -> _decs.apply(o.name()).cs().stream()).map(T.C::name).toList();
    return cs.stream().filter(c -> !indirect.contains(c.name())).toList();
  }
  private static List<T> asTs(List<B> bs){ return bs.stream().<T>map(b -> new T.X(b.x(), TSpan.fromPos(Pos.unknown))).toList(); }
  boolean sigs(Literal l, M m, boolean always){
    var fm= TypeSystemErrors.srcM(l, m.sig());
    var sources= direct(l.cs()).stream().filter(c -> own(c.name(), m.sig()).isPresent()).toList();
    if (fm.isEmpty() || sources.isEmpty() || TypeSystemErrors.wholeSig(fm.get(), m.sig())){ return false; }
    return sigs(expRepr(l), sources, sources.stream().map(c -> inherited(c, m.sig())).toList(), always);
  }
  private Sig inherited(T.C c, Sig s){
    var o= own(c.name(), s).get();
    var xs= Push.of(B.xs(_decs.apply(c.name()).bs()), B.xs(o.bs()));
    var ts= Push.of(c.ts(), asTs(s.bs()));
    return new Sig(o.rc(), o.m(), s.bs(), TypeRename.ofT(o.ts(), xs, ts), TypeRename.of(o.ret(), xs, ts), o.origin(), o.abs(), o.span());
  }
  boolean sigs(String who, List<T.C> heads, List<Sig> ss, boolean always){
    var original= Streams.zip(heads, ss).map((h,s) -> originals(h.name(), s)).toList();
    var renamed= Streams.zip(original, ss).anyMatch((os,s) -> os.stream().anyMatch(o -> !B.xs(o.bs()).equals(B.xs(s.bs()))));
    if (!renamed && !always){ return false; }
    var flat= original.stream().flatMap(List::stream).toList();
    if (renamed){ bulletsByCount("Original signature", "Original signatures", sigLines(flat.stream().map(o -> head(_decs.apply(o.origin()))).toList(), flat)); }
    bulletsByCount("Signature as inherited by "+who, "Signatures as inherited by "+who, sigLines(heads, ss));
    return true;
  }
  private List<Sig> originals(TName n, Sig s){
    var d= _decs.apply(n);
    var o= own(n, s);
    if (o.isEmpty()){ return List.of(); }
    var sig= o.get();
    var written= d.src() == Src.synthetic ? sig.origin().equals(n) : sig.bs().isEmpty() || TypeSystemErrors.srcM(d, sig).flatMap(fearlessFullGrammar.M::sig).flatMap(fearlessFullGrammar.Sig::bs).isPresent();
    if (written){ return List.of(new Sig(sig.rc(), sig.m(), sig.bs(), sig.ts(), sig.ret(), n, sig.abs(), sig.span())); }
    return direct(d.cs()).stream().flatMap(c -> originals(c.name(), s).stream()).toList();
  }
  private void bulletsByCount(String one, String many, List<String> lines){ bullets((lines.size() == 1 ? one : many)+":", lines); }
  private static T.C head(Literal d){ return new T.C(d.name(), asTs(d.bs())); }
  private List<String> sigLines(List<T.C> heads, List<Sig> ss){ return Streams.zip(heads, ss).map(this::sigLine).distinct().toList(); }
  private String sigLine(T.C h, Sig s){
    var sig= cp().sig(s);
    return sig.substring(0, CompactPrinter.rcWidth)+cp().msgT(new T.RCC(RC.imm, h, h.span()))+sig.substring(CompactPrinter.rcWidth);
  }
  static String and(List<String> xs){
    if (xs.size() == 1){ return xs.getFirst(); }
    return Join.of(xs.subList(0, xs.size()-1), "", ", ", "")+" and "+xs.getLast();
  }
  String expRepr(E toErr){ return switch (toErr){
    case Call c -> "method call "+methodSig(c.name());
    case X x -> "parameter "+disp(x.src().inner instanceof fearlessFullGrammar.E.Implicit ? "::" : x.name());
    case Literal l -> l.thisName().equals("this")
      ? "type declaration "+tNameADisp(l.name())
      : "object literal "+(showInstanceOf(l) ? "instance of " : "")+disp(bestLitName(l));
    case Type(var t, _) -> "object literal instance of "+typeRepr(true, t.withRC(RC.imm));
    };}
  String expReprDirect(boolean skipImm, E toErr, RC rc){ return switch (toErr){
    case Literal l -> disp((anonLit(l) ? "" : rc.toStrSpace(skipImm))+bestLitName(l));
    case Type(var t, _) -> typeRepr(skipImm, t.withRC(rc));
    default -> throw Bug.unreachable();
    };}
  String expRepr(inference.E toErr){ return switch (toErr){
    case inference.E.Call c -> "method call "+methodSig(c.name());
    case inference.E.X(var name, _, _, _) -> "parameter "+disp(name);
    case inference.E.Literal l -> l.thisName().equals("this")
      ? "type declaration "+tNameADisp(l.name())
      : l.infName() && bestName(l).equals(l.name()) ? "object literal "+disp(anonRepr)
      : "object literal "+(l.infName() ? "instance of " : "")+tNameADisp(bestName(l));
    case inference.E.Type t -> "object literal instance of "+tNameADisp(t.type().c().name());
    };}
  static String methodSig(MName m){ return methodSig("", m); }
  String methodSig(String pre, Literal l, MName m){ return methodSig(pre+bestLitName(l), m); }
  String methodSig(String pre, inference.E.Literal l, MName m){ return methodSig(pre+tNameA(bestName(l)), m); }
  static String methodSig(String pre, MName m){ return disp(Join.of(Collections.nCopies(m.arity(), "_"), pre+m.s()+"(", ",", ")", pre+m.s())); }
  String text(){ return sb.toString().stripTrailing(); }
  Err line(String s){
    assert !s.isEmpty();
    assert sb.lastIndexOf("\n") == sb.length()-1;
    s = s.stripTrailing();
    sb.append(s).append("\n");
    return this;
  }
  Err blank(){
    var n= sb.length();
    assert sb.charAt(n-1) == '\n';
    if (sb.charAt(n-2) != '\n'){ sb.append('\n'); }
    return this;
  }
  Err list(String heading, List<String> items){
    assert !items.isEmpty();
    if (items.size() == 1){ return line(heading+": "+items.getFirst()+"."); }
    return bullets(heading+":", items);
  }
  Err didYouMean(List<String> options){
    assert !options.isEmpty();
    if (options.size() == 1){ return line("Did you mean "+options.getFirst()+" ?"); }
    return bullets("Did you mean one of the following?", options);
  }
  Err bullets(String heading, List<String> items){
    line(heading);
    items.forEach(this::bullet);
    return this;
  }
  Err bullet(String s){
    assert !s.isBlank();
    return line("- "+s.replace("\n", "\n  "));
  }
  Err pCallCantBeSatisfied(Literal d, Call c){
    return line("This call to method "+methodSig(c.rc().toStrSpace(), d, c.name())+" cannot typecheck.");
  }
  Err pCallCantBeSatisfied(Call c){
    return line("This call to method "+methodSig(c.name())+" cannot typecheck.");
  }
  Err selfNameDeadCode(String self, String litRepr){
    return line("The self name "+disp(self)+" is dead code.").line("No method of the "+litRepr+" uses it.").line("Remove "+disp("'"+self)+" from the object literal.");
  }
  Err standalone(){ return line("A type is standalone if it is declared at top level, or if it implements "+tNameADisp(LiteralDeclarations.captureFree)+"."); }
  String gotMsg(boolean skipImm, String label, List<T> got, T expected){
    return label+" has type "+Join.of(got.stream().map(t -> typeRepr(skipImm, t)), "", " or ", "")
      +" instead of a subtype of "+typeRepr(skipImm, expected)+".";
  }
  FearlessException ex(E e){ return ex(e, e); }
  FearlessException typeErr(){ return withNotes(Code.TypeError, ""); }
  FearlessException ex(E footerE, E focus){ return ex(footerE, focus, List.of()); }
  FearlessException ex(E footerE, E focus, List<T> inferred){
    var ts= Push.of(inferred, chainInferredTargs(focus)).stream().map(t -> typeRepr(true, t)).distinct().toList();
    if (ts.isEmpty()){ return typeErr(); }
    var quietCp= cpOf.apply(true);
    var footer= quietCp.limit(footerE, focus);
    var header= "See inferred typing context below for how "+and(ts)+(ts.size() == 1 ? " was" : " were")+" introduced"+(quietCp.omitted ? " (\"...\" marks omitted code):\n" : ":\n");
    return withNotes(Code.TypeError, "\n\n"+header+footer);
  }
  private static List<T> chainInferredTargs(E e){
    if (!(e instanceof Call c)){ return List.of(); }
    return Push.of(targsInferred(c) ? c.targs() : List.of(), chainInferredTargs(c.e()));
  }
  static boolean targsInferred(Call c){
    var written= c.src().inner instanceof fearlessFullGrammar.E.Call(_, _, var sq, _, _, _, _) && sq.filter(s -> !s.ts().isEmpty()).isPresent();
    return !c.targs().isEmpty() && !written;
  }
  FearlessException wf(){
    assert sb.length() != 0;
    return withNotes(Code.WellFormedness, "");
  }
  private FearlessException withNotes(Code code, String footer){
    var body= text();
    return code.of(() -> body+Join.of(notes.get().stream(), "\n\n", "\n", "", "")+footer);
  }
}