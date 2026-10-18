package compact;
import static compact.Frontend.TK.*;
import static compact.Frontend.RC.*;
import static java.util.Optional.*;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;
import java.util.function.*;
import java.util.regex.Pattern;
import java.util.stream.*;
public final class Frontend{ @SuppressWarnings("serial") public static final class Fail extends RuntimeException{}
  static void ck(boolean b){ if (b){ throw new Fail(); } } static boolean dup(List<?> l){ return l.stream().distinct().count() < l.size(); }
  public static final class H<V>{ public V inner; H(V inner){ this.inner= inner; } @Override public boolean equals(Object o){ return o instanceof H; }
    @Override public int hashCode(){ return 0; } } static <V> List<V> push(List<V> a, List<V> b){ return Stream.concat(a.stream(), b.stream()).toList(); }
  static <V> List<V> push(List<V> a, V b){ return Stream.concat(a.stream(), Stream.of(b)).toList(); }
  static <V> List<V> push(V a, List<V> b){ return Stream.concat(Stream.of(a), b.stream()).toList(); }
  static <A,B,R> Stream<R> zip(List<A> as, List<B> bs, BiFunction<A,B,R> f){ return IntStream.range(0, as.size()).mapToObj(i -> f.apply(as.get(i), bs.get(i))); }
  @SafeVarargs @SuppressWarnings("varargs") static <V> Stream<V> cat(Stream<V>... ss){ return Stream.of(ss).flatMap(s -> s); }
  static String join(List<?> l, String start, String sep, String end, String empty){
    return l.isEmpty() ? empty : l.stream().map(Object::toString).collect(Collectors.joining(sep, start, end)); }
  static String join(Stream<?> l, String start, String sep, String end, String empty){ return join(l.toList(), start, sep, end, empty); }
  public static Object parse(String input){ return new Parser(new Names(List.of(), List.of(), List.of()), tokens(input)).parseAll(Parser::parseFileFull); }
  public static List<Literal> compile(String pkgName, Map<String,String> override, Map<String,String> files, List<Literal> otherLits){
    var other= otherLits.stream().collect(Collectors.toMap(Literal::name, d -> d)); var raw= new TreeMap<String,FileFull>();
    files.forEach((path, content) -> raw.put(path, (FileFull)parse(content)));
    var heads= raw.keySet().stream().filter(p -> { var name= p.substring(p.lastIndexOf('/')+1); var dot= name.lastIndexOf('.'); return dot > 0 && name.substring(0, dot).startsWith("_rank_"); }).toList();
    ck(heads.size() != 1); var head= raw.get(heads.getFirst());
    ck(raw.entrySet().stream().anyMatch(e -> !e.getKey().equals(heads.getFirst()) && !e.getValue().noDirectives()));
    var ds= raw.values().stream().flatMap(f -> f.decs().stream()).toList();
    var names= DeclaredNames.of(pkgName, ds, head.uses().stream().map(FileFull.Use::out).collect(Collectors.toUnmodifiableSet()));
    var map= new HashMap<>(override); for (var u : head.uses()){ var p= map.getOrDefault(u.in().pkgName(), u.in().pkgName());
      var in= p + "." + u.in().simpleName(); map.put(u.out(), in);
      var dom= p.equals(pkgName) ? names.decNames().stream().map(n -> n.withPkgName(pkgName)) : other.keySet().stream();
      ck(dom.noneMatch(e -> e.s().equals(in))); } var ctx= new Methods(new Pkg(pkgName, Collections.unmodifiableMap(map), ds, names), other);
    var res= InjectionSteps.steps(ctx, ctx.registerTypeHeadersAndReturnRoots(toInference(ctx))); TypeSystem.allOk(res, other); return res; } public enum RC{
    imm, mut, read, iso, mutH, readH; boolean isSubType(RC other){ if (this == other || other == readH){ return true; } return switch (this){
        case mut -> other == mutH || other == read; case imm -> other == read; case iso -> true; case readH, read, mutH -> false; }; }
    boolean isH(){ return this == mutH || this == readH; } boolean isReadOrImm(){ return this == read || this == imm; }
    boolean isIsoOrImm(){ return this == iso || this == imm; } RC isoToMut(){ return this == iso ? mut : this; }
    RC readImm(){ return isIsoOrImm() ? imm : read; } String toStrSpace(){ return this == imm ? "" : this+" "; } } public record TName(String s, int arity){
    static int pkgDot(String s){ return s.contains(".") && s.charAt(0) >= 'a' && s.charAt(0) <= 'z' ? s.indexOf('.') : -1; }
    TName withPkgName(String pkg){ return new TName(pkg+"."+s, arity); } TName withoutPkgName(){ return new TName(simpleName(), arity); }
    TName withArity(int arity){ return new TName(s, arity); } @Override public String toString(){ return s+"/"+arity; }
    String pkgName(){ var i= pkgDot(s); return i == -1 ? "" : s.substring(0, i); }
    String simpleName(){ var i= pkgDot(s); return i == -1 ? s : s.substring(i + 1); } boolean isPublic(){ return !simpleName().startsWith("_"); } }
  public record MName(String s, int arity){ MName withArity(int arity){ return new MName(s, arity); } @Override public String toString(){ return s; } }
  public record B(String x, EnumSet<RC> rcs){ static List<String> xs(List<B> bs){ return bs.stream().map(B::x).toList(); }
    static B get(List<B> bs, String name){ return bs.stream().filter(b -> b.x().equals(name)).findFirst().get(); }
    @Override public String toString(){ return x+":"+join(rcs.stream().map(RC::name), "", ",", "", ""); } }
  public record Sig(RC rc, MName m, List<B> bs, List<IT> ts, IT ret, TName origin, boolean abs){
    @Override public String toString(){ return " "+rc.toStrSpace()+m+join(bs, "[", ",", "]", "")+join(ts, "(", ",", ")", "")+":"+ret+"@"+origin.s()+";"; } }
  public record M(Sig sig, List<String> xs, Optional<E> e){ M withSig(Sig sig){ return new M(sig, xs, e); } @Override public String toString(){
      return sig.rc().toStrSpace()+sig.m()+join(sig.bs(), "[", ",", "]", "")+join(zip(xs, sig.ts(), (x,t) -> x+":"+t), "(", ", ", ")", "")
        +":"+sig.ret()+e.map(body -> "->"+body).orElse(""); } } public sealed interface E{ default Stream<E> children(){ return switch (this){
      case X _, Type _ -> Stream.of(); case Literal l -> l.ms().stream().flatMap(m -> m.e().stream());
      case Call c -> Stream.concat(Stream.of(c.e()), c.es().stream()); };}
    record X(String name) implements E{ @Override public String toString(){ return name; } }
    record Type(IT.RCC type) implements E{ @Override public String toString(){ return type.toString();} }
    record Call(E e, MName name, RC rc, List<IT> targs, List<E> es, H<IT> expectedRes) implements E{
      @Override public String toString(){ return ""+e+name+join(targs, "["+rc+",", ",", "", "["+rc)+"]"+join(es, "(", ", ", ")", ""); } } }
  public record Literal(RC rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, boolean infName, H<Boolean> onlyImmCapture) implements E{
    Literal(RC rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, boolean infName){ this(rc, name, bs, cs, thisName, ms, infName, new H<>(false)); }
    Literal withMs(List<M> ms){ return new Literal(rc, name, bs, cs, thisName, ms, infName, onlyImmCapture); }
    Literal withRC(RC rc){ return new Literal(rc, name, bs, cs, thisName, ms, infName, onlyImmCapture); }
    @Override public String toString(){ return rc+" "+name.s()+join(bs, "[", ",", "]", "")+":"+join(cs, "", ", ", "", "")+"{'"+thisName+" "+join(ms, "", "; ", "", "")+"}"; }
  } enum TK{
    Ws("\\s+"), LineComment("//[^\\n]*"), BlockComment("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"), BadUnclosedBlockComment("(?s)/\\*(?!.*?\\*/).*"), BadUnopenedBlockCommentClose("\\*/"),
    Arrow("->"), ORound("\\("), CRound("\\)"), OCurly("\\{"), CCurlyId("\\}[A-Za-z0-9_]+'*"), CCurly("\\}"),
    OSquareArg("(?<=[A-Za-z0-9_'`\\x22\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])(?<!\\x2A/)\\["), BadOSquare("\\["), CSquare("\\]"),
    Underscore("_"), Comma(","), SemiColon(";"), ColonColon("::"), Colon(":"), Eq("="), SQuote("'"), ReadImm("read/imm"), RCap("readH|mutH|imm|iso|read|mut"),
    SignedFloat("[+-](?:[0-9](?:[0-9_]*[0-9])?)\\.(?:[0-9](?:[0-9_]*[0-9])?)(?:[eE][+-]?[0-9](?:[0-9_]*[0-9])?)?(?:soft)?"),
    UnSignedFloat("[0-9](?:[0-9_]*[0-9])?\\x2E(?:[0-9](?:[0-9_]*[0-9])?)(?:[eE][\\x2B\\x2D]?[0-9](?:[0-9_]*[0-9])?)?(?:soft)?"),
    SignedInt("[+-][0-9](?:[0-9_]*[0-9])?"), UnsignedInt("[0-9](?:[0-9_]*[0-9])?"),
    BadUStrUnclosed("\\x22[^\\x22\\x0A]*(?=\\x0A|\\z)"), BadSStrUnclosed("`[^`\\x0A]*(?=\\x0A|\\z)"), UStr("\\x22[^\\x22\\x0A]*\\x22"), SStr("`[^`\\x0A]*`"),
    DotName("\\._*[a-z][A-Za-z0-9_]*'*"), UppercaseId("(?:"+TK.pkg+"\\x2E)?_*[A-Z][A-Za-z0-9_]*'*"), BadUppercaseId("(?:[a-z][a-z0-9_]*\\x2E)?_*[A-Z][A-Za-z0-9_]*'*"),
    LowercaseId("_*[a-z][A-Za-z0-9_]*'*"), BadSStrQuote("'(?:(?!//|/\\x2A)[^'\\x0A\\x22`])*'(?![_a-z])"), Op("(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])+"),
    _XId("_*[A-Z][A-Za-z0-9_]*'*"), _pkgName(TK.pkg), _use("use"), _map("map"), _as("as"), _in("in"),
    _EOF(""), _SOF(""), _All(""), _CurlyGroup(""), _SquareGroup(""), _RoundGroup("");
    static final String pkg= "(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*"; final Pattern p;
    TK(String regex){ p= Pattern.compile(regex); }
    int match(String s, int i){ var m= p.matcher(s).useTransparentBounds(true).region(i, s.length()); return m.lookingAt() ? m.end()-i : -1; } }
  static boolean isKind(String input, TK... kinds){ return Stream.of(kinds).anyMatch(k -> k.match(input, 0) == input.length()); }
  static final TK[] typeName= {UppercaseId, SignedFloat, UnSignedFloat, SignedInt, UnsignedInt, SStr, UStr};
  record Token(TK kind, String content, List<Token> tokens){ boolean is(TK... kinds){ return Stream.of(kinds).anyMatch(k -> k == kind); } }
  static final String allowed= "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>,.;:()[]{}`'\"!?@#$%^&_|~\\ \n";
  static final Map<TK,Map<TK,TK>> groups= Map.of(_SOF, Map.of(_EOF, _All), ORound, Map.of(CRound, _RoundGroup), OSquareArg, Map.of(CSquare, _SquareGroup), OCurly, Map.of(CCurly, _CurlyGroup, CCurlyId, _CurlyGroup));
  static final Map<TK,Set<TK>> barriers= Map.of(ORound, Set.of(SemiColon, Arrow, SQuote), OSquareArg, Set.of(SemiColon, Arrow, SQuote, LowercaseId, ORound, OCurly, DotName));
  static List<Token> tokens(String s){ if (s.startsWith("\uFEFF")){ s = s.substring(1); }
    s = s.replace("\r\n", "\n").replace('\r', '\n').replace('\u2028', '\n').replace('\u2029', '\n').replace('\u0085', '\n');
    ck(s.codePoints().anyMatch(c -> allowed.indexOf(c) < 0)); var all= new ArrayList<Token>(); for (int i= 0; i < s.length();){ TK best= null; int len= 0;
      for (var k : TK.values()){ var l= k.name().startsWith("_") ? -1 : k.match(s, i); if (l > len){ best= k; len= l; } } ck(best == null);
      all.add(new Token(best, s.substring(i, i+len), List.of())); i += len; } var res= new ArrayList<Token>(List.of(new Token(_SOF, "", List.of())));
    for (int i= 0; i < all.size(); i++){ var t= all.get(i); if (t.is(Ws, LineComment, BlockComment)){ continue; }
      var bad= t.is(BadUStrUnclosed, BadSStrUnclosed, BadUnclosedBlockComment, BadUnopenedBlockCommentClose, BadOSquare, BadUppercaseId, BadSStrQuote)
        || t.is(OSquareArg) && all.get(i-1).is(SStr, UStr, SignedInt, UnsignedInt, SignedFloat, UnSignedFloat); ck(bad); res.add(t); }
    res.add(new Token(_EOF, "", List.of())); var it= res.iterator(); return tree(it, it.next()).tokens(); } static Token tree(Iterator<Token> it, Token open){
    var out= new ArrayList<Token>(List.of(open)); while (true){ var c= it.next(); ck(barriers.getOrDefault(open.kind(), Set.of()).contains(c.kind()));
      var g= groups.get(open.kind()).get(c.kind()); if (g != null){ out.add(c); return new Token(g, "", out); }
      if (groups.containsKey(c.kind())){ out.add(tree(it, c)); continue; } ck(groups.values().stream().anyMatch(m -> m.containsKey(c.kind()))); out.add(c); } }
  sealed interface PE{ record X(String name) implements PE{} record Round(PE e) implements PE{}
    record Lit(Optional<PE.X> thisName, List<PM> methods) implements PE{} record TypedLiteral(IT.RCC t, Optional<Lit> l) implements PE{}
    record DeclarationLiteral(Optional<RC> rc, Declaration dec) implements PE{} record CallSquare(Optional<RC> rc, List<IT> ts){}
    record Call(PE e, MName name, Optional<CallSquare> targs, boolean pars, Optional<XPat> pat, List<PE> es) implements PE{} record Implicit() implements PE{} }
  record PSig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, boolean hasParenthesis, List<Parameter> parameters, Optional<IT> t){
    PSig withImplicit(){ return new PSig(rc, m.map(mi -> mi.withArity(parameters.size()+1)), bs, hasParenthesis, parameters, t); } }
  record PM(Optional<PSig> sig, Optional<PE> body, boolean hasImplicit, H<Object> span){
    PM(Optional<PSig> sig, Optional<PE> body){ this(sig, body, body.stream().anyMatch(Frontend::hasImplicit), new H<>(null)); }
    PM{ if (hasImplicit){ sig = sig.map(PSig::withImplicit); } } } static boolean hasImplicit(PE e){ return switch (e){
    case PE.X _, PE.TypedLiteral _, PE.DeclarationLiteral _, PE.Lit _ -> false; case PE.Round(var inner) -> hasImplicit(inner); case PE.Implicit _ -> true;
    case PE.Call c -> hasImplicit(c.e()) || c.es().stream().anyMatch(Frontend::hasImplicit); };} record Parameter(Optional<XPat> xp, Optional<IT> t){}
  sealed interface XPat{ Stream<String> parameterNames();
    record Name(PE.X x) implements XPat{ @Override public Stream<String> parameterNames(){ return Stream.of(x.name()); } }
    record Destruct(List<List<MName>> extract, Optional<String> id) implements XPat{
      @Override public Stream<String> parameterNames(){ return extract.stream().map(e -> e.getLast().s().substring(1) + id.orElse("")); } } }
  record Declaration(TName name, Optional<List<B>> bs, List<IT.C> cs, PE.Lit l){}
  record FileFull(List<FileFull.Map> maps, List<Use> uses, List<Declaration> decs){ record Use(TName in, String out){}
    record Map(String in, String out, String target){} boolean noDirectives(){ return maps.isEmpty() && uses.isEmpty(); } }
  record Names(List<String> xs, List<String> Xs, List<String> hiddenXs){
    Names add(List<String> xs, List<String> Xs){ return new Names(push(this.xs, xs), push(this.Xs, Xs), hiddenXs); } }
  record RCMName(Optional<RC> rc, MName name){} static final class Parser{ Names names; final List<Token> ts; int index= 0; int limit;
    Parser(Names names, List<Token> ts){ this.names= names; this.ts= ts; limit= ts.size(); }
    Parser make(List<Token> tokens){ return new Parser(names, tokens); } <R> R parseAll(Function<Parser,R> r){ var res= r.apply(this); ck(index != limit);
      return res; } boolean end(){ return limit == index; }
    Optional<Token> peek(int la){ var i= index + la; return i < 0 || i >= limit ? empty() : of(ts.get(i)); }
    boolean peek(TK... kinds){ return peekIf(t -> t.is(kinds)); } boolean peekIf(Predicate<Token> p){ return peek(0).map(p::test).orElse(false); }
    @SafeVarargs final boolean peekOrder(Predicate<Token>... ps){ return IntStream.range(0, ps.length).allMatch(i -> peek(i).filter(ps[i]).isPresent()); }
    Token expect(TK... kinds){ var t= peek(0).orElseThrow(Fail::new); ck(kinds.length > 0 && !t.is(kinds)); index += 1; return t; }
    Token expectLast(TK... kinds){ ck(limit == 0 || !ts.get(limit - 1).is(kinds)); limit -= 1; return ts.get(limit); }
    void expectEnd(){ if (!end()){ throw new Fail(); } } boolean fwdIf(boolean v){ if (v){ index += 1; } return v; } <R> R parseGroup(Function<Parser,R> r){
      var res= make(ts.get(index).tokens()).parseAll(r); index += 1; return res; } <R> List<R> splitBy(ToIntFunction<Parser> probe, Function<Parser,R> elem){
      var slice= ts.subList(index, limit); var sp= make(slice); var parts= new ArrayList<Parser>(); while (!sp.end()){ int start= sp.index;
        int drop= probe.applyAsInt(sp); ck(drop < 0 || start > sp.index-drop || start >= sp.index);
        parts.add(make(List.copyOf(slice.subList(start, sp.index-drop)))); } index = limit; return parts.stream().map(p -> p.parseAll(elem)).toList(); }
    <R> List<R> parseGroupSep(Function<Parser,R> r, TK open, TK close, ToIntFunction<Parser> probe){
      return parseGroup(p -> { p.expect(open); p.expectLast(close); return p.splitBy(probe, r); }); }
    <R> Optional<R> parseFront(boolean emptyAllowed, ToIntFunction<Parser> probe, Function<Parser,R> first){ var slice= ts.subList(index, limit);
      var sp= make(slice); int drop= probe.applyAsInt(sp); int end= sp.index; ck(drop < 0 || 0 > end-drop || !emptyAllowed && end <= 0);
      if (sp.end()){ return empty(); } var res= make(List.copyOf(slice.subList(0, end-drop))).parseAll(first); index += end; return of(res); }
    int splitOn(int mode, TK k){ fwdIf(index != 0 && !end() && mode == 2); while (!end()){ if (!expect().is(k)){ continue; }
        if (mode == 2){ index -= 1; return 0; } return mode; } return 0; } PE parseE(){ var e= parseAtom(); while (!end()){ e = parsePost(e); } return e; }
    boolean hasPost(){ return peek(DotName, Op, Colon); }
    boolean isDec(){ return peekOrder(t -> t.is(typeName), t -> t.is(_SquareGroup), t -> t.is(Colon)) || peekOrder(t -> t.is(typeName), t -> t.is(Colon)); }
    PE parseAtom(){ if (peek(LowercaseId)){ return parseX(); }
      if (peek(_RoundGroup)){ return parseGroup(p -> { p.expect(ORound); p.expectLast(CRound); return new PE.Round(p.parseE()); }); }
      if (peek(ColonColon)){ expect(); return new PE.Implicit(); } if (peek(_CurlyGroup)){ return parseGroup(p -> p.parseLiteral(false)); }
      var rc= parseOptRC(); ck(rc.stream().anyMatch(RC::isH)); if (isDec()){ return new PE.DeclarationLiteral(rc, parseDeclaration(false)); }
      ck(!peek(typeName)); var c= new IT.RCC(of(rc.orElse(RC.imm)), parseC());
      return new PE.TypedLiteral(c, parseIf(peek(_CurlyGroup), () -> parseGroup(p -> p.parseLiteral(false)))); }
    RC parseRC(){ return RC.valueOf(expect(RCap).content()); } Optional<RC> parseOptRC(){ return parseIf(peek(RCap), this::parseRC); } IT.C parseC(){
      var c= parseTName(); if (!peek(_SquareGroup)){ return new IT.C(c, List.of()); } var ts= parseGroupSep(Parser::parseT, OSquareArg, CSquare, commaSkip);
      return new IT.C(c.withArity(ts.size()), ts); } TName parseTName(){ var s= expect(typeName).content();
      ck(names.Xs().contains(s) || names.hiddenXs().contains(s)); var res= new TName(s, 0); ck(!res.pkgName().isEmpty() && !res.isPublic()); return res; }
    IT parseT(){ if (fwdIf(peek(ReadImm))){ return new IT.ReadImmX(parseTX(false, false)); } var rc= parseOptRC();
      if (peekIf(t -> t.is(typeName) && !names.Xs().contains(t.content()))){ return new IT.RCC(of(rc.orElse(RC.imm)), parseC()); }
      var res= parseTX(false, false); return rc.map(r -> (IT)new IT.RCX(r, res)).orElse(res); } IT.X parseTX(boolean dec, boolean mustNew){
      var c= expectValidate(UppercaseId, _XId).content(); ck(dec && mustNew ? names.Xs().contains(c) || names.hiddenXs().contains(c) : !names.Xs().contains(c));
      return new IT.X(c); } PE parsePost(PE receiver){ if (peek(SignedFloat, SignedInt)){ var num= expect().content();
        var rcc= new IT.RCC(of(RC.imm), new IT.C(new TName(num.substring(1), 0), List.of()));
        return new PE.Call(receiver, new MName(num.substring(0, 1), 1), empty(), false, empty(), List.of(new PE.TypedLiteral(rcc, empty()))); }
      var m= new MName(expect(DotName, Op).content(), 0); var sq= parseIf(peek(_SquareGroup), () -> parseGroup(Parser::parseCallSquare));
      if (peek(_RoundGroup)){ var es= parseGroupSep(Parser::parseE, ORound, CRound, Parser::onCommaExp);
        return new PE.Call(receiver, m.withArity(es.size()), sq, true, empty(), es); }
      var xpat= parseIf(eqSugar(), () -> { var r= parseXPat(); index += 1; return r; }); if (end() || hasPost()){ ck(xpat.isPresent());
        return new PE.Call(receiver, m, sq, false, empty(), List.of()); } var atom= parseAtom(); var xs= xsOf(xpat).toList(); checkNewXs(xs);
      ck(xpat.isPresent() && xpat.get() instanceof XPat.Destruct && xs.size() > 31); names = names.add(xs, List.of());
      if (xpat.isPresent()){ atom = parsePost(atom); while (!end()){ atom = parsePost(atom); } }
      return new PE.Call(receiver, m.withArity(xpat.isPresent() ? 2 : 1), sq, false, xpat, List.of(atom)); } boolean eqSugar(){
      if (peekOrder(t -> t.is(Underscore), t -> t.is(Eq))){ var last= peek(-1).get(); if (last.is(_SquareGroup)){ last = peek(-2).get(); }
        ck(last.is(DotName, Op)); } return peekOrder(t -> t.is(LowercaseId, _CurlyGroup), t -> t.is(Eq)); } XPat parseXPat(){
      if (peek(LowercaseId, Underscore)){ return new XPat.Name(parseDecX()); } var res= parseGroup(Parser::parseDestruct);
      if (!peek(LowercaseId, UnsignedInt, UppercaseId)){ return res; } throw new Fail(); } XPat.Destruct parseDestruct(){ expect(OCurly);
      var last= expectLast(CCurly, CCurlyId).content(); var id= parseIf(last.length()>1, () -> last.substring(1));
      var chains= splitBy(commaSkip, p -> p.splitBy(q -> { q.expect(); return 0; }, q -> new MName(q.expect(DotName).content(), 0)));
      ck(chains.isEmpty() || chains.stream().anyMatch(List::isEmpty)); var res= new XPat.Destruct(chains, id);
      ck(res.parameterNames().anyMatch(x -> !isKind(x, LowercaseId) || isKind(x, RCap))); return res; } PE.CallSquare parseCallSquare(){ expect(OSquareArg);
      var hasRC= peekOrder(t -> t.is(RCap), t -> t.is(Comma, CSquare)); expectLast(CSquare); var rc= parseIf(hasRC, this::parseRC);
      if (hasRC && !end()){ expect(Comma); } return new PE.CallSquare(rc, end() ? List.of() : splitBy(commaSkip, Parser::parseT)); } PE.X parseX(){
      var x= expect(LowercaseId).content(); ck(!names.xs().contains(x)); return new PE.X(x); } PE.X parseDecX(){
      var x= expect(LowercaseId, Underscore).content(); ck(names.xs().contains(x)); return new PE.X(x); } PE.Lit parseLiteral(boolean top){ expect(OCurly);
      expectLast(CCurly); var thisName= parseIf(fwdIf(peek(SQuote)), this::parseDecX); var n= thisName.map(PE.X::name).orElse(top ? "this" : "_");
      ck(top && !n.equals("this")); if (!n.equals("_")){ names = names.add(List.of(n), List.of()); } for (int i= 0; peek(i).isPresent(); i += 1){
        ck(peek(i).get().is(SemiColon) && (i == 0 || peek(i-1).get().is(SemiColon))); }
      var ms= splitBy(p -> p.splitOn(1, SemiColon), p -> { var res= p.parseMethod(top); p.expectEnd(); return res; });
      var ns= ms.stream().flatMap(m -> m.sig().flatMap(s -> s.m().map(nn -> new RCMName(s.rc(), nn))).stream()).toList(); ck(dup(ns));
      ck(ns.stream().anyMatch(nn -> nn.rc().isEmpty() && ns.stream().anyMatch(o -> o.name().equals(nn.name()) && o.rc().isPresent())));
      var noNames= ms.stream().filter(m -> m.sig().flatMap(PSig::m).isEmpty()).map(m -> m.sig().map(s -> s.parameters().size()).orElse(0) + (m.hasImplicit() ? 1 : 0)).toList();
      ck(dup(noNames)); return new PE.Lit(thisName, ms); }
    Stream<String> xsOf(Optional<XPat> xp){ return xp.stream().flatMap(XPat::parameterNames).filter(x -> !x.equals("_")); } void checkNewXs(List<String> xs){
      for (int i= 0; i < xs.size(); i++){ if (names.xs().contains(xs.get(i)) || xs.subList(0, i).contains(xs.get(i))){ throw new Fail(); } } }
    PM parseMethodWithSig(PSig sig){ var xs= sig.parameters().stream().flatMap(p -> xsOf(p.xp())).toList(); checkNewXs(xs);
      names = names.add(xs, bsXs(sig.bs())); var m= new PM(of(sig), of(parseMethodBody()));
      var hasPats= sig.parameters().stream().flatMap(p -> p.xp().stream()).anyMatch(XPat.Destruct.class::isInstance);
      ck(hasPats && xs.size() + (m.hasImplicit() ? 1 : 0) > 32); return m; }
    static List<String> bsXs(Optional<List<B>> bs){ return bs.orElse(List.of()).stream().map(B::x).toList(); } PM parseMethod(boolean top){
      var m= parseFront(false, p -> p.splitOn(1, Arrow), Parser::parseSig).map(this::parseMethodWithSig); if (m.isPresent()){ return m.get(); }
      var hasSig= peek(DotName, Op) || peekOrder(t -> t.is(RCap), t -> t.is(DotName, Op)); if (!hasSig){ return new PM(empty(), of(parseMethodBody())); }
      var sig= parseSig(); ck(!top); return new PM(of(sig), empty()); } PE parseMethodBody(){ make(ts.subList(index, limit)).checkAbruptExprEnd();
      var res= make(ts.subList(index, limit)).parseAll(Parser::parseE); index = limit; return res; } PSig parseSig(){ var rc= parseOptRC();
      ck(rc.stream().anyMatch(r -> r.isH() || r == RC.iso)); ck(peekOrder(t -> t.is(LowercaseId), t -> t.is(_RoundGroup, _SquareGroup)));
      var m= parseIf(peek(DotName, Op), () -> new MName(expect(DotName, Op).content(), 0)); var bs= parseIf(peek(_SquareGroup), () -> parseBs(true));
      names = names.add(List.of(), bsXs(bs)); var hasPar= peek(_RoundGroup);
      var ps= hasPar ? parseGroupSep(Parser::parseParameter, ORound, CRound, commaSkip) : peek(Colon) ? List.<Parameter>of() : splitBy(commaSkip, Parser::parseParameter);
      var t= parseIf(fwdIf(peek(Colon)), this::parseT); m = m.map(_m -> _m.withArity(ps.size())); var xs= ps.stream().flatMap(p -> xsOf(p.xp())).toList();
      ck(dup(xs)); return new PSig(rc, m, bs, hasPar, ps, t); } Parameter parseParameter(){
      var x= parseIf(peek(LowercaseId, Underscore, _CurlyGroup), this::parseXPat);
      var p= new Parameter(x, x.isPresent() ? parseIf(fwdIf(peek(Colon)), this::parseT) : of(parseT())); expectEnd(); return p; }
    List<B> parseBs(boolean mustNew){ return parseGroup(p -> { p.expect(OSquareArg); p.expectLast(CSquare);
        var res= p.splitBy(Parser::onCommaB, pi -> pi.parseB(mustNew)); var Xs= bsXs(of(res)); ck(dup(Xs)); return res; }); } B parseB(boolean mustNew){
      var x= parseTX(true, mustNew).name(); if (end()){ return new B(x, EnumSet.of(RC.imm)); } expect(Colon); ck(end()); if (!peek(Op)){
        var rcs= splitBy(commaSkip, Parser::parseRC); ck(dup(rcs)); return new B(x, rcs.isEmpty() ? EnumSet.of(RC.imm) : EnumSet.copyOf(rcs)); }
      return switch (expect(Op).content()){ case "**" -> new B(x, EnumSet.allOf(RC.class)); case "*" -> new B(x, EnumSet.of(RC.imm, RC.mut, RC.read));
        default -> throw new Fail(); }; } Declaration parseDeclaration(boolean top){
      var nonDecl= peek(RCap, DotName, Op, _RoundGroup, _CurlyGroup, _SquareGroup, LowercaseId, Underscore, ColonColon, SStr, UStr, SignedInt, SignedFloat, UnSignedFloat, UnsignedInt);
      ck(top && (peek(SemiColon) || !peek(typeName) && nonDecl)); var c= parseTName(); index -= 1; expectValidate(UppercaseId, _XId);
      var bs= parseIf(peek(_SquareGroup), () -> parseBs(top)); var Xs= bsXs(bs); var outer= names;
      names = top ? names.add(List.of(), Xs) : new Names(names.xs(), Xs, push(names.hiddenXs(), names.Xs())); c = c.withArity(Xs.size()); expect(Colon);
      var cs= parseFront(true, p -> p.splitOn(2, _CurlyGroup), p -> p.splitBy(commaSkip, Parser::parseC)).orElseThrow(Fail::new); ck(dup(cs));
      var l= parseGroup(p -> p.parseLiteral(top)); names = outer; return new Declaration(c, bs, cs, l); } FileFull parseFileFull(){ expect(_SOF);
      expectLast(_EOF); var maps= new ArrayList<FileFull.Map>(); var uses= new ArrayList<FileFull.Use>(); Function<Parser,Object> header= p -> {
        if (!p.peek(LowercaseId)){ return ""; } p.expectLast(SemiColon); return p.splitBy(q -> q.splitOn(1, SemiColon), q -> q.parseHeaderElement(maps, uses));
      }; if (parseFront(true, Parser::headEnd, header).isEmpty()){ parseAll(header); }
      var ds= splitBy(p -> p.splitOn(0, _CurlyGroup), p -> p.parseDeclaration(true)); return new FileFull(List.copyOf(maps), List.copyOf(uses), ds); }
    Token expectValidate(TK kind, TK validation){ ck(!peekIf(t -> isKind(t.content(), validation))); return expect(kind); }
    Object parseHeaderElement(ArrayList<FileFull.Map> maps, ArrayList<FileFull.Use> uses){ if (fwdIf(peekIf(t -> isKind(t.content(), _map)))){
        var in= expectValidate(LowercaseId, _pkgName).content(); expectValidate(LowercaseId, _as); var out= expectValidate(LowercaseId, _pkgName).content();
        expectValidate(LowercaseId, _in); var target= expectValidate(LowercaseId, _pkgName).content();
        ck(maps.stream().anyMatch(m -> m.in().equals(in) && m.target().equals(target))); maps.add(new FileFull.Map(in, out, target)); } else{
        ck(!fwdIf(peekIf(t -> isKind(t.content(), _use)))); var t1= parseTName(); expectValidate(LowercaseId, _as);
        var t2= expectValidate(UppercaseId, _XId).content(); ck(uses.stream().anyMatch(u -> u.in().equals(t1) || u.out().equals(t2)));
        uses.add(new FileFull.Use(t1, t2)); } expectEnd(); return null; }
    <R> Optional<R> parseIf(boolean cond, Supplier<R> s){ return cond ? of(s.get()) : empty(); } int onCommaExp(){ var inColon= false; while (!end()){
        var t= expect(); if (t.is(Comma) && !inColon){ return 1; } if (!t.is(_SquareGroup, Comma, UppercaseId)){ inColon = false; }
        if (t.is(Colon)){ inColon = true; } } return 0; } int onCommaB(){ while (!end()){ if (expect().is(Comma) && !peek(RCap)){ return 1; } } return 0; }
    int headEnd(){
      while (!(end() || isDec() || peek(_CurlyGroup, _RoundGroup, _SquareGroup) || peekOrder(t -> t.is(typeName), t -> t.is(_SquareGroup, _CurlyGroup, _RoundGroup)))){ expect(); }
      return 0; } void checkAbruptExprEnd(){ ck(peek(Colon, Arrow, SQuote, Eq, Comma, SemiColon, Underscore, ReadImm)); eatAtom(); while (!end()){
        if (peek(SignedInt, SignedFloat)){ expect(); continue; } ck(!fwdIf(hasPost())); fwdIf(peek(_SquareGroup)); eatAtom(); } } void eatAtom(){
      if (eqSugar()){ expect(); expect(); } if (fwdIf(peek(LowercaseId, _RoundGroup, ColonColon, _CurlyGroup))){ return; } fwdIf(peek(RCap));
      fwdIf(peekOrder(t -> t.is(typeName))); fwdIf(peek(_SquareGroup));
      if (fwdIf(peek(Colon))){ while (fwdIf(peek(UppercaseId, SignedFloat, UnSignedFloat, SignedInt, UnsignedInt, SStr, UStr, Comma, _SquareGroup))){} }
      fwdIf(peek(_CurlyGroup)); } static final ToIntFunction<Parser> commaSkip= p -> p.splitOn(1, Comma); }
  record Pkg(String name, Map<String,String> map, List<Declaration> decs, DeclaredNames names){}
  record DeclaredNames(Set<TName> decNames, Map<TName,Set<String>> allXs, Map<TName,Set<String>> allParameters){
    static DeclaredNames of(String pkgName, List<Declaration> ds, Set<String> uses){ var decNames= new LinkedHashSet<TName>();
      var Xs= new LinkedHashMap<TName,Set<String>>(); var xs= new LinkedHashMap<TName,Set<String>>(); for (var d : ds){ var names= new LinkedHashSet<String>();
        var bXs= new LinkedHashSet<String>(); new Object(){ void dec(Declaration d){ ck(!decNames.add(d.name()));
            d.bs().ifPresent(bs -> bs.forEach(b -> bXs.add(b.x()))); lit(d.l()); } void lit(PE.Lit c){ c.thisName().ifPresent(n -> names.add(n.name()));
            for (var m : c.methods()){ m.sig().ifPresent(s -> { s.bs().ifPresent(bs -> bs.forEach(b -> bXs.add(b.x())));
                s.parameters().forEach(p -> p.xp().ifPresent(x -> x.parameterNames().forEach(names::add))); }); m.body().ifPresent(this::e); } } void e(PE e){
            switch (e){ case PE.X _, PE.Implicit _ -> {} case PE.Round(var inner) -> e(inner); case PE.TypedLiteral(_, var l) -> l.ifPresent(this::lit);
              case PE.DeclarationLiteral(_, var dec) -> dec(dec); case PE.Lit c -> lit(c);
              case PE.Call c -> { e(c.e()); c.pat().ifPresent(x -> x.parameterNames().forEach(names::add)); c.es().forEach(this::e); } } } }.dec(d);
        var n= d.name().withPkgName(pkgName); xs.put(n, Collections.unmodifiableSet(names)); Xs.put(n, Collections.unmodifiableSet(bXs)); }
      var decStrs= decNames.stream().map(TName::s).toList(); ck(!Collections.disjoint(decStrs, uses));
      var allNames= Stream.concat(decStrs.stream(), uses.stream()).toList();
      ck(!Collections.disjoint(allNames, Xs.values().stream().flatMap(Set::stream).toList()));
      return new DeclaredNames(Collections.unmodifiableSet(decNames), Collections.unmodifiableMap(Xs), Collections.unmodifiableMap(xs)); } }
  record OwnerState(HashSet<String> gen, HashMap<String,Integer> genSeq, HashSet<String> vars, HashMap<String,Integer> varSeq){}
  record FreshPrefix(HashSet<String> usedTopTypes, HashMap<String,Integer> topSeq, HashSet<String> allGenericNames, HashMap<TName,OwnerState> owners, String pkgName){
    FreshPrefix(Pkg p){ this(new HashSet<>(), new HashMap<>(), new HashSet<>(), new HashMap<>(), p.name());
      for (var tn : p.names().decNames()){ usedTopTypes.add(tn.simpleName()); } usedTopTypes.addAll(p.map().keySet()); var xs= p.names().allXs();
      for (var owner : xs.keySet()){ var genNames= new HashSet<String>(xs.get(owner)); allGenericNames.addAll(genNames);
        owners.put(owner, new OwnerState(genNames, new HashMap<>(), new HashSet<>(p.names().allParameters().get(owner)), new HashMap<>())); } }
    TName freshTopType(TName hint, int arity){
      var res= new TName(pkgName+"."+freshCandidate(hint.simpleName(), "ABCDEFGHJKMNPQRSTUVWXYZ", topSeq, usedTopTypes, List.of(allGenericNames)), arity);
      owners.put(res, owners.get(hint)); return res; }
    boolean isFreshGeneric(TName owner, String x, List<String> scope){ return !owners.get(owner).gen().contains(x) && !usedTopTypes.contains(x) && !scope.contains(x); }
    String freshGeneric(TName owner, String hint, List<String> siblings){ var st= owners.get(owner);
      var cand= freshCandidate(hint, "ABCDEFGHJKMNPQRSTUVWXYZ", st.genSeq(), st.gen(), List.of(usedTopTypes, siblings)); allGenericNames.add(cand); return cand;
    } String freshVar(TName owner, String hint){ var st= owners.get(owner);
      return freshCandidate(hint, "abcdefghjkmnpqrstuvwxyz", st.varSeq(), st.vars(), List.of()); }
    static String freshCandidate(String hint, String alphabet, HashMap<String,Integer> seq, HashSet<String> commitScope, List<Collection<String>> extraChecks){
      var base= hint.replaceAll("[^A-Za-z0-9]", ""); if (base.length() > 4){ base = base.substring(0, 4); } for (int n= seq.getOrDefault(base, 1);; n += 1){
        var sb= new StringBuilder(); for (int k= n; k > 0; k = (k-1) / alphabet.length()){ sb.append(alphabet.charAt((k-1) % alphabet.length())); }
        var cand= "_"+sb.reverse()+base; if (commitScope.contains(cand) || extraChecks.stream().anyMatch(e -> e.contains(cand))){ continue; }
        commitScope.add(cand); seq.put(base, n+1); return cand; } } }
  static final TName baseStr= new TName("base.Str", 0), baseNat= new TName("base.Nat", 0), baseInt= new TName("base.Int", 0), baseFloat= new TName("base.Float", 0),
    widen= new TName("base.WidenTo", 1), sealed= new TName("base.Sealed", 0), captureFree= new TName("base.CaptureFree", 0), baseId= new TName("base.BaseId", 2),
    baseContainer= new TName("base.BaseContainer", 1), inferUnknown= new TName("base.InferUnknown", 0);
  static final List<TName> inferErrs= List.of(new TName("base.InferErr", 2), new TName("base.InferErr", 3), new TName("base.InferErr", 4));
  static boolean has(List<IT.C> cs, TName magic){ return cs.stream().anyMatch(c -> c.name().equals(magic)); }
  static boolean isPrimitiveLiteral(String name){ return "+-1234567890\"`".contains(name.substring(0, 1)); }
  static Literal from(TName n, Function<TName,Literal> map, Map<TName,Literal> other){ var res= map.apply(n); if (res == null){ res = other.get(n); }
    if (res != null || !n.pkgName().equals("base") || !isPrimitiveLiteral(n.simpleName())){ return res; } var s= n.simpleName();
    var lit= s.startsWith("`") || s.startsWith("\"") ? baseStr : isKind(s, UnsignedInt) ? baseNat : isKind(s, SignedInt) ? baseInt : baseFloat;
    var sup= from(lit, map, other);
    var ms= sup.ms().stream().map(m -> m.withSig(new Sig(m.sig().rc(), m.sig().m(), m.sig().bs(), m.sig().ts(), m.sig().ret(), n, false))).toList();
    return new Literal(RC.imm, n, List.of(), push(new IT.C(lit, List.of()), sup.cs()), "this", ms, true); }
  static BigInteger big(String raw){ return new BigInteger(raw.replace("_", "")); }
  static boolean inRange(String raw, BigInteger min, BigInteger max){ return big(raw).compareTo(min) >= 0 && big(raw).compareTo(max) <= 0; }
  static boolean floatOk(String raw){ var soft= raw.endsWith("soft"); var ns= (soft ? raw.substring(0, raw.length()-4) : raw).replace("_", "");
    var d= Double.parseDouble(ns); if (soft){ return Double.isFinite(d); } if (ns.startsWith("+")){ ns = ns.substring(1); }
    if (!Double.isFinite(d)){ return false; } if (d == 0){ return new BigDecimal(ns.replaceAll("[eE].*", "")).signum() == 0; }
    return new BigDecimal(ns).compareTo(new BigDecimal(d)) == 0; } public sealed interface IT{ default boolean isTV(){ return true; }
    default long badness(){ return 0; } default Optional<RC> explicitRC(){ return Optional.empty(); } default int depth(){ return 1; }
    record X(String name) implements IT{ @Override public String toString(){ return name; } } record RCX(RC rc, X x) implements IT{
      @Override public String toString(){ return rc.name()+" "+x.name; } @Override public Optional<RC> explicitRC(){ return Optional.of(rc); } }
    record ReadImmX(X x) implements IT{ @Override public String toString(){ return "read/imm "+x.name; } } record C(TName name, List<IT> ts, int depth){
      C(TName name, List<IT> ts){ this(name, ts, RCC.depthFromTs(ts)); } @Override public String toString(){ return name.s()+join(ts, "[", ",", "]", ""); } }
    record RCC(Optional<RC> rc, C c) implements IT{ public RCC{ if (c.depth() > 100){ throw new Fail(); } }
      static int depthFromTs(List<IT> ts){ return 1+ts.stream().mapToInt(IT::depth).max().orElse(1); } RCC withTs(List<IT> ts){ return withRCTs(rc, ts); }
      RCC withRCTs(Optional<RC> rc, List<IT> ts){ var depth= depthFromTs(ts); return depth > 100 ? this : new RCC(rc, new C(c.name(), ts, depth)); }
      @Override public long badness(){ return c.ts.stream().mapToLong(IT::badness).sum(); }
      @Override public String toString(){ return rc.map(RC::toStrSpace).orElse("AnyRC ")+c; }
      @Override public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); } @Override public int depth(){ return c.depth(); }
      @Override public Optional<RC> explicitRC(){ return rc; } } enum U implements IT{ Instance; @Override public String toString(){ return "?";}
      @Override public boolean isTV(){ return false; } @Override public long badness(){ return 1; } } default IT withRC(RC rc){ return switch (this){
      case RCC(_, var c) -> new RCC(Optional.of(rc), c); case RCX(_, var x) -> new RCX(rc, x); case X x -> new RCX(rc, x);
      case ReadImmX(var x) -> new RCX(rc, x); case U _ -> this; };} default Stream<String> ftv(){ return switch (this){ case X(var name) -> Stream.of(name);
      case RCX(_, var x) -> x.ftv(); case ReadImmX(var x) -> x.ftv(); case RCC(_, var c) -> c.ts().stream().flatMap(IT::ftv); case U _ -> Stream.of(); };}
    default IT readImm(){ return switch (this){ case X x -> new ReadImmX(x); case ReadImmX _ -> this;
      case RCC(var rc, var c) -> new RCC(rc.map(RC::readImm), c); case RCX(var rc, var x) -> new RCX(rc.readImm(), x); case U _ -> this; };} }
  static final class GSig{ Object snap; @Override public boolean equals(Object o){ return o instanceof GSig; } @Override public int hashCode(){ return 0; } }
  sealed interface IE{ IT t(); IE withT(IT t); GSig g(); record X(String name, IT t, GSig g) implements IE{
      X(String name){ this(name, IT.U.Instance, new GSig()); } @Override public IE withT(IT t){ return t.equals(this.t) ? this : new X(name, t, new GSig()); } }
    record Type(IT.RCC type, IT t, GSig g) implements IE{ Type(IT.RCC type){ this(type, IT.U.Instance, new GSig()); }
      @Override public IE withT(IT t){ return t.equals(this.t) ? this : new Type(type, t, new GSig()); } }
    record Lit(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<IM> ms, IT t, boolean bsWritten, boolean infName, boolean infHead, GSig g) implements IE{
      Lit(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<IM> ms, boolean bsWritten, boolean infName){
        this(rc, name, bs, cs, thisName, ms, IT.U.Instance, bsWritten, infName, false, new GSig()); }
      @Override public Lit withT(IT t){ return t.equals(this.t) ? this : new Lit(rc, name, bs, cs, thisName, ms, t, bsWritten, infName, infHead, new GSig()); }
      Lit withMsT(List<IM> ms, IT t){ if (infHead && ms == this.ms && t.equals(this.t)){ return this; }
        return new Lit(rc, name, bs, cs, thisName, ms, t, bsWritten, infName, true, new GSig()); } Lit withCsMs(List<IT.C> cs, List<IM> ms, boolean setInfHead){
        if (infHead == setInfHead && cs.equals(this.cs) && ms == this.ms){ return this; }
        return new Lit(rc, name, bs, cs, thisName, ms, t, bsWritten, infName, setInfHead, new GSig()); } }
    record Call(IE e, MName name, Optional<RC> rc, List<IT> targs, List<IE> es, IT t, boolean written, GSig g) implements IE{
      Call(IE e, MName name, Optional<RC> rc, List<IT> targs, List<IE> es, boolean written){ this(e, name, rc, targs, es, IT.U.Instance, written, new GSig()); }
      Call withMore(IE e, RC rc, List<IT> targs, List<IE> es, IT t){
        if (e == this.e && this.rc.equals(Optional.of(rc)) && targs.equals(this.targs) && es == this.es && t.equals(this.t)){ return this; }
        return new Call(e, name, Optional.of(rc), targs, es, t, written, new GSig()); }
      Call withEEs(IE e, List<IE> es){ return e == this.e && es == this.es ? this : new Call(e, name, rc, targs, es, t, written, new GSig()); }
      @Override public Call withT(IT t){ return t.equals(this.t) ? this : new Call(e, name, rc, targs, es, t, written, new GSig()); } }
    record ICall(IE e, MName name, List<IE> es, IT t, GSig g) implements IE{
      ICall(IE e, MName name, List<IE> es){ this(e, name, es, IT.U.Instance, new GSig());}
      @Override public IE withT(IT t){ return t.equals(this.t) ? this : new ICall(e, name, es, t, new GSig()); }
      IE withEEs(IE e, List<IE> es){ return e == this.e && es == this.es ? this : new ICall(e, name, es, t, new GSig()); } } }
  record IM(ISig sig, Optional<Impl> impl){ IM withSig(ISig sig){ return sig.equals(this.sig) ? this : new IM(sig, impl); } }
  record ISig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Optional<IT>> ts, Optional<IT> ret, Optional<TName> origin, boolean abs, H<Object> span){
    ISig(RC rc, MName m, List<B> bs, List<Optional<IT>> ts, IT ret, TName origin, boolean abs, H<Object> span){
      this(Optional.of(rc), Optional.of(m), Optional.of(bs), ts, Optional.of(ret), Optional.of(origin), abs, span); }
    ISig withTsT(List<Optional<IT>> ts, IT ret){ return new ISig(rc, m, bs, ts, Optional.of(ret), origin, abs, span); }
    ISig withOrigin(TName origin){ return new ISig(rc, m, bs, ts, ret, Optional.of(origin), abs, span); } }
  record Impl(Optional<MName> m, List<String> xs, IE e){ Impl withE(IE e){ return e == this.e ? this : new Impl(m, xs, e); } } static final class IGamma{
    record Frame(RC rc, List<B> bs, LinkedHashMap<String,IT> vars){}
    final ArrayList<Frame> fs= new ArrayList<>(List.of(new Frame(null, List.of(), new LinkedHashMap<>())));
    int at(String x){ return IntStream.range(0, fs.size()).filter(i -> fs.get(i).vars().containsKey(x)).findFirst().orElse(-1); }
    IT get(String x){ var i= at(x); return i == -1 ? null : fs.get(i).vars().get(x); } IT getWithRC(String x){ var i= at(x); var t= get(x);
      for (var s= i + 1; s < fs.size(); s += 1){ t = adapt(t, fs.get(s).rc(), fs.get(s).bs()); } return t; } boolean notFunnelledInto(String x){
      var fxs= get(x).ftv().toList(); return IntStream.range(at(x) + 1, fs.size()).anyMatch(s -> !B.xs(fs.get(s).bs()).containsAll(fxs)); }
    static IT adapt(IT t, RC rc, List<B> bs){ var x= t instanceof IT.X(var n) ? n : t instanceof IT.ReadImmX(IT.X(var n)) ? n : null; if (x != null){
        var xRcs= B.get(bs, x).rcs(); if (rc == RC.imm || EnumSet.of(RC.iso, RC.imm).containsAll(xRcs)){ return t.withRC(RC.imm); }
        if (xRcs.stream().anyMatch(RC::isH)){ return t; } return rc == RC.read || xRcs.contains(RC.iso) ? t.readImm() : t; } var trc= t.explicitRC();
      if (rc == RC.imm || trc.equals(Optional.of(RC.iso))){ return t.withRC(RC.imm); } if (rc == RC.mut){ return t; }
      if (trc.equals(Optional.of(RC.mutH))){ return t.withRC(RC.readH); } return trc.equals(Optional.of(RC.mut)) ? t.withRC(RC.read) : t; }
    void declare(String x, IT t){ if (!x.equals("_")){ fs.getLast().vars().put(x, t); } }
    Object snap(){ var m= new HashMap<String,IT>(); fs.forEach(f -> m.putAll(f.vars())); return m; } }
  static IT norm(Optional<IT> t){ return t.map(Frontend::norm).orElse(inferUnknownT); }
  static IT.C normC(IT.C c){ return new IT.C(c.name(), c.ts().stream().map(Frontend::norm).toList()); } static IT norm(IT t){ return switch (t){
    case IT.RCC(var rc, var c) -> new IT.RCC(of(rc.orElse(RC.imm)), normC(c)); case IT.U _ -> inferUnknownT; default -> t; };}
  static final IT.RCC inferUnknownT= new IT.RCC(of(RC.imm), new IT.C(inferUnknown, List.of())); static IT renameT(IT t, List<String> xs, List<IT> ts){
    return switch (t){ case IT.X x -> xs.contains(x.name()) ? ts.get(xs.indexOf(x.name())) : x;
      case IT.RCX(var rc, var x) -> { var r= renameT(x, xs, ts); yield isInfer(r) ? r : r.withRC(rc); }
      case IT.RCC(var rc, var c) -> new IT.RCC(rc, new IT.C(c.name(), c.ts().stream().map(ti -> renameT(ti, xs, ts)).toList()));
      case IT.ReadImmX(var x) -> { var r= renameT(x, xs, ts); yield isInfer(r) ? r : r.readImm(); } case IT.U _ -> t; }; }
  static boolean isInfer(IT t){ return t instanceof IT.RCC(_, var c) && (c.name().equals(inferUnknown) || inferErrs.contains(c.name())); }
  static IT rename(IT t, List<String> xs, List<IT> ts){ return switch (t){ case IT.X x -> xs.contains(x.name()) ? ts.get(xs.indexOf(x.name())) : x;
      case IT.RCX(var rc, var x) -> rename(x, xs, ts).withRC(rc); case IT.RCC rcc -> rcc.withTs(renameIT(rcc.c().ts(), xs, ts));
      case IT.ReadImmX(var x) -> rename(x, xs, ts).readImm(); case IT.U _ -> t; }; }
  static List<IT> renameIT(List<IT> tsi, List<String> xs, List<IT> ts){ return tsi.stream().map(ti -> rename(ti, xs, ts)).toList(); }
  static List<IT> toXs(List<String> xs){ return xs.stream().<IT>map(IT.X::new).toList(); }
  static List<IT> qMarks(int n){ return Stream.<IT>generate(() -> IT.U.Instance).limit(n).toList(); }
  record MSigL(RC rc, List<String> xs, List<B> clsBs, List<IT> clsArgs, List<B> methBs, List<IT> ps0, IT ret0){
    MSigL withClsArgs(List<IT> clsArgs){ return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0); }
    IT inst(IT t, List<IT> targs){ return rename(t, xs, push(clsArgs, fixTargs(targs, methBs.size()))); }
    static List<IT> fixTargs(List<IT> targs, int n){ return targs.size() > n ? targs.subList(0, n) : push(targs, qMarks(n-targs.size())); } }
  static Stream<String> ftvE(IGamma g, IE e){ return switch (e){
    case IE.X(var name, var t, _) -> Stream.concat(t.ftv(), Stream.ofNullable(g.get(name)).flatMap(IT::ftv));
    case IE.Lit l -> cat(l.bs().stream().map(B::x), ftvCs(l.cs()), ftvMs(g, l.ms()));
    case IE.Call(var ei, _, _, var targs, var es, _, _, _) -> cat(ftvE(g, ei), targs.stream().flatMap(IT::ftv), es.stream().flatMap(x -> ftvE(g, x)));
    case IE.ICall(var ei, _, var es, _, _) -> Stream.concat(ftvE(g, ei), es.stream().flatMap(x -> ftvE(g, x))); case IE.Type(var t, _, _) -> t.ftv(); };}
  static Stream<String> ftvCs(List<IT.C> cs){ return cs.stream().flatMap(c -> c.ts().stream().flatMap(IT::ftv)); }
  static Stream<String> ftvMs(IGamma g, List<IM> ms){ return ms.stream().flatMap(m -> { var domBs= B.xs(m.sig().bs().orElse(List.of()));
      return cat(m.sig().ts().stream().flatMap(o -> o.stream().flatMap(IT::ftv)), m.sig().ret().stream().flatMap(IT::ftv), m.impl().stream().flatMap(i -> ftvE(g, i.e()))).filter(x -> !domBs.contains(x));
    }); } static IE dup(FreshPrefix fresh, IE e){ return switch (e){ case IE.X(var name, var t, _) -> new IE.X(name, t, new GSig());
    case IE.Type(var type, var t, _) -> new IE.Type(type, t, new GSig());
    case IE.ICall c -> new IE.ICall(dup(fresh, c.e()), c.name(), c.es().stream().map(x -> dup(fresh, x)).toList(), c.t(), new GSig());
    case IE.Call c -> new IE.Call(dup(fresh, c.e()), c.name(), c.rc(), c.targs(), c.es().stream().map(x -> dup(fresh, x)).toList(), c.t(), c.written(), new GSig());
    case IE.Lit l -> { ck(!l.infName()); var newName= fresh.freshTopType(l.name(), l.name().arity());
      yield new IE.Lit(l.rc(), newName, l.bs(), l.cs(), l.thisName(), l.ms().stream().map(m -> dupM(fresh, m, l.name(), newName)).toList(), l.t(), l.bsWritten(), true, l.infHead(), new GSig());
    } };} static IM dupM(FreshPrefix fresh, IM m, TName oldName, TName newName){
    var sig= m.sig().origin().equals(Optional.of(oldName)) ? m.sig().withOrigin(newName) : m.sig();
    return new IM(sig, m.impl().map(i -> new Impl(i.m(), i.xs(), dup(fresh, i.e())))); } static List<IE.Lit> toInference(Methods meths){ var p= meths.p;
    Function<TName,TName> f= tn -> { var pN= tn.pkgName(); if (pN.isEmpty() && isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
      var mapped= pN.isEmpty() ? p.map().get(tn.s()) : null;
      var full= pN.isEmpty() ? (mapped == null ? tn.withPkgName(p.name()) : new TName(mapped, tn.arity())) : new TName(p.map().getOrDefault(pN, pN)+"."+tn.simpleName(), tn.arity());
      var ok= full.pkgName().equals(p.name()) ? p.names().decNames().contains(full.withoutPkgName()) : pN.isEmpty() ? meths.other.containsKey(full) : meths.other.get(full) != null;
      ck(!ok); return full; }; var decs= new ArrayList<IE.Lit>(); for (var di : p.decs()){ var name= f.apply(di.name());
      new Visitor(meths, name, new ArrayList<>(), f, decs).addDeclaration(name, RC.mut, di, true); } return List.copyOf(decs); } record XE(String x, PE e){}
  record Visitor(Methods meths, TName currentTop, ArrayList<String> implicits, Function<TName,TName> f, ArrayList<IE.Lit> decs){
    IT visitT(IT t){ return t instanceof IT.RCC(var rc, var c) ? new IT.RCC(rc, visitC(c)) : t; } IE visitE(PE e){ return switch (e){
        case PE.X x -> new IE.X(x.name()); case PE.Round(var inner) -> visitE(inner); case PE.Implicit n -> new IE.X(implicits.getLast());
        case PE.TypedLiteral t -> { if (t.l().isEmpty()){ yield new IE.Type((IT.RCC)visitT(t.t())); } var impl= List.of(visitC(t.t().c()));
          var ms= t.l().get().methods().stream().map(this::visitM).toList();
          var l= liftLiteral(of(t.t().rc().orElse(RC.imm)), impl, t.l().get().thisName().map(n -> n.name()), ms); decs.add(l); yield l; }
        case PE.DeclarationLiteral c -> { var name= f.apply(c.dec().name()); meths.fresh.owners().put(name, meths.fresh.owners().get(currentTop));
          yield addDeclaration(name, c.rc().orElse(RC.imm), c.dec(), false); } case PE.Lit l -> visitLiteral(l); case PE.Call c0 -> {
          var c= c0.pat().isPresent() ? desugarCPat(c0) : c0; var recv= visitReceiver(c.e()); var es= c.es().stream().map(this::visitE).toList();
          yield c.targs().isEmpty() ? new IE.ICall(recv, c.name(), es) : new IE.Call(recv, c.name(), c.targs().get().rc(), c.targs().get().ts().stream().map(this::visitT).toList(), es, true);
        } }; } IT.C visitC(IT.C c){ var s= c.name().s();
      var bad= isPrimitiveLiteral(s) && (isKind(s, UnsignedInt) && !inRange(s, BigInteger.ZERO, new BigInteger(Long.toUnsignedString(-1L)))
        || isKind(s, SignedInt) && !inRange(s, BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE))
        || isKind(s, SignedFloat, UnSignedFloat) && !floatOk(s)); ck(bad); return new IT.C(f.apply(c.name()), c.ts().stream().map(this::visitT).toList()); }
    String parameterToName(Parameter p, boolean hasPat){ if (p.xp().isEmpty()){ return "_"; } return switch (p.xp().get()){
        case XPat.Name(var x) -> hasPat && !x.name().equals("_") ? meths.fresh.freshVar(currentTop, x.name()) : x.name();
        case XPat.Destruct _ -> meths.fresh.freshVar(currentTop, "div"); }; } IM visitM(PM m){ return new IM(visitMSig(m), visitMImpl(m)); }
    ISig visitMSig(PM mm){
      if (mm.sig().isEmpty()){ return new ISig(empty(), empty(), empty(), mm.hasImplicit() ? List.of(empty()) : List.of(), empty(), empty(), false, mm.span()); }
      var s= mm.sig().get(); var ts= s.parameters().stream().map(p -> p.t().map(this::visitT)).toList(); if (mm.hasImplicit()){ ts = push(ts, empty()); }
      return new ISig(s.rc(), s.m(), s.bs(), ts, s.t().map(this::visitT), empty(), mm.body().isEmpty(), mm.span()); } Optional<Impl> visitMImpl(PM m){
      if (m.body().isEmpty()){ return empty(); } var body= m.body().get(); var original= m.sig().map(s -> s.parameters()).orElse(List.of());
      var hasPat= original.stream().anyMatch(p -> p.xp().stream().anyMatch(XPat.Destruct.class::isInstance));
      var ps= original.stream().map(p -> parameterToName(p, hasPat)).toList();
      var xpats= zip(ps, original, (x,p) -> p.xp().stream().flatMap(xp -> xpat(xp, x))).flatMap(s -> s).toList(); if (m.hasImplicit()){
        var p= meths.fresh.freshVar(currentTop, "impl"); var inner= hasPat ? meths.fresh.freshVar(currentTop, "impl") : p; ps = push(ps, p);
        if (hasPat){ xpats = push(xpats, new XE(inner, new PE.X(p))); } implicits.add(inner); } if (hasPat){
        var pps= xpats.stream().map(xe -> new Parameter(of(new XPat.Name(new PE.X(xe.x))), empty())).toList();
        var fl= new PE.Lit(empty(), List.of(new PM(of(new PSig(empty(), empty(), empty(), false, pps, empty())), of(body), false, new H<>(null))));
        body = new PE.Call(new PE.TypedLiteral(new IT.RCC(of(RC.imm), new IT.C(new TName("base.Destruct", 0), List.of())), empty()), new MName("#", xpats.size()+1), empty(), true, empty(), push(xpats.stream().map(XE::e).toList(), fl));
      } var e= visitE(body); if (m.hasImplicit()){ implicits.removeLast(); } return of(new Impl(m.sig().flatMap(s -> s.m()), ps, e)); }
    Stream<XE> xpat(XPat xp, String lowered){ return switch (xp){ case XPat.Destruct d -> zip(d.extract(), d.parameterNames().toList(), (e,x) -> {
        PE res= new PE.X(lowered); for (var m : e){ res = new PE.Call(res, new MName(m.s(), 0), empty(), true, empty(), List.of()); } return new XE(x, res); });
      case XPat.Name(var x) -> x.name().equals(lowered) ? Stream.of() : Stream.of(new XE(x.name(), new PE.X(lowered))); };}
    IE.Lit liftLiteral(Optional<RC> rc, List<IT.C> impl, Optional<String> thisName, List<IM> ms){
      return new IE.Lit(rc, meths.fresh.freshTopType(currentTop, 0), List.of(), impl, thisName.orElse("_"), ms, false, true); } IE visitReceiver(PE e){
      var s= e; while (s instanceof PE.Round(var inner)){ s = inner; } if (!(s instanceof PE.Lit ol)){ return visitE(e); } var l= visitLiteral(ol); decs.add(l);
      return l; }
    IE.Lit visitLiteral(PE.Lit l){ return liftLiteral(empty(), List.of(), l.thisName().map(n -> n.name()), l.methods().stream().map(this::visitM).toList()); }
    IE.Lit addDeclaration(TName name, RC rc, Declaration d, boolean top){ var thisName= d.l().thisName().map(n -> n.name()).orElseGet(() -> top ? "this" : "_");
      var bs= d.bs().orElse(List.of()); var cs= d.cs().stream().map(this::visitC).toList();
      ck(duplicatedSupertypes(bs, cs.stream().map(Frontend::normC).toList()));
      var l= new IE.Lit(of(rc), name, bs, cs, thisName, d.l().methods().stream().map(this::visitM).toList(), d.bs().isPresent(), false); decs.add(l); return l;
    } PE.Call desugarCPat(PE.Call c){ var fresh= new PE.X(meths.fresh.freshVar(currentTop, "eqS")); var par1= c.es().getFirst();
      var res= replaceAtom(par1, fresh); while (par1 instanceof PE.Call ci){ par1 = ci.e(); }
      var sig= new PSig(empty(), empty(), empty(), false, List.of(new Parameter(c.pat(), empty()), new Parameter(of(new XPat.Name(fresh)), empty())), empty());
      var par2= new PE.Lit(empty(), List.of(new PM(of(sig), of(res), false, new H<>(null))));
      return new PE.Call(c.e(), c.name(), c.targs(), true, empty(), List.of(par1, par2)); } PE replaceAtom(PE par, PE atom){
      if (!(par instanceof PE.Call c)){ return atom; } return new PE.Call(replaceAtom(c.e(), atom), c.name(), c.targs(), c.pars(), c.pat(), c.es()); } }
  static boolean duplicatedSupertypes(List<B> bs, List<IT.C> cs){ var ts= cs.stream().map(c -> new IT.RCC(of(RC.imm), c)).toList();
    return IntStream.range(0, ts.size()).anyMatch(j -> IntStream.range(0, j).anyMatch(i -> TypeSystem.isSameShapeSubtype(bs, ts.get(i), ts.get(j)) && TypeSystem.isSameShapeSubtype(bs, ts.get(j), ts.get(i))));
  } static final class Methods{
    final Pkg p; final Map<TName,Literal> other; final FreshPrefix fresh; final LinkedHashMap<TName,Literal> cache= new LinkedHashMap<>();
    Methods(Pkg p, Map<TName,Literal> other){ this.p= p; this.other= other; fresh= new FreshPrefix(p); }
    List<IE.Lit> registerTypeHeadersAndReturnRoots(List<IE.Lit> iDecs){ var rem= new LinkedHashMap<TName,IE.Lit>();
      for (var d : iDecs){ if (!d.infName()){ rem.put(d.name(), d); } } var acc= new ArrayList<IE.Lit>(); while (!rem.isEmpty()){
        var layer= rem.values().stream().filter(d -> d.cs().stream().noneMatch(c -> c.name().pkgName().equals(p.name()) && rem.containsKey(c.name()))).toList();
        ck(layer.isEmpty()); for (var d : layer){ rem.remove(d.name()); var e= expandDeclaration(d, false); if (d.thisName().equals("this")){ acc.add(e); }
          register(e); } } return List.copyOf(acc); } List<IT.C> fetchCs(IT.C c){ var d= from(c.name()); if (d == null){ return List.of(); }
      return d.cs().stream().map(ci -> new IT.C(ci.name(), renameIT(ci.ts(), B.xs(d.bs()), c.ts()))).distinct().toList(); }
    List<ISig> fetchSigs(IE.Lit child, IT.C c, Literal d, List<String> scope){ return d.ms().stream().map(m -> alphaSig(m, d, c, child, scope)).toList(); }
    ISig alphaSig(M m, Literal d, IT.C c, IE.Lit child, List<String> scope){ var s= m.sig(); var fullXs= new ArrayList<>(B.xs(d.bs()));
      var fullTs= new ArrayList<>(c.ts()); var newBs= new ArrayList<B>(s.bs().size()); for (var b : s.bs()){ var x= b.x();
        if (fresh.isFreshGeneric(child.name(), x, scope)){ newBs.add(b); continue; } fullXs.add(x);
        var newX= new IT.X(fresh.freshGeneric(child.name(), x, push(B.xs(s.bs()), scope))); fullTs.add(newX); newBs.add(new B(newX.name(), b.rcs())); }
      var newTs= renameIT(s.ts(), fullXs, fullTs).stream().map(Optional::of).toList();
      return new ISig(s.rc(), s.m(), Collections.unmodifiableList(newBs), newTs, rename(s.ret(), fullXs, fullTs), s.origin(), s.abs(), new H<>(null)); }
    Literal from(TName name){ return Frontend.from(name, cache::get, other); } IE.Lit expandDeclaration(IE.Lit d, boolean setInfHead){
      var ds= d.cs().stream().map(c -> fetchSigs(d, c, from(c.name()), List.of())).toList();
      var implied= d.cs().stream().flatMap(c -> fetchCs(c).stream()).toList();
      var allCs= ToCore.distinctTypes(d.bs(), push(d.cs(), implied.stream().sorted(Comparator.comparing(Object::toString)).toList()));
      var allSig= zip(d.cs(), ds, (c,sigs) -> implied.contains(c) ? Stream.<ISig>of() : sigs.stream()).flatMap(s -> s).toList();
      var res= d.withCsMs(allCs, pairWithSig(inferMNames(d.ms(), new ArrayList<>(allSig)), new ArrayList<>(allSig), d), setInfHead);
      checkMagicSupertypes(res, allCs); return res; } IE.Lit expandLiteral(IE.Lit d, IT.C c, List<B> scope){ var dd= from(c.name());
      List<ISig> allSig= dd == null ? List.of() : fetchSigs(d, c, dd, B.xs(scope));
      return d.withCsMs(push(c, fetchCs(c)), pairWithSig(inferMNames(d.ms(), new ArrayList<>(allSig)), new ArrayList<>(allSig), d), true); }
    void checkMagicSupertypes(IE.Lit d, List<IT.C> allCs){ ck(allCs.stream().filter(c -> c.name().equals(widen)).count() > 1);
      if (allCs.stream().anyMatch(c -> c.name().equals(baseId))){ var ms= d.ms();
        ck(ms.size() != 1 || !ms.getFirst().sig().m().get().equals(new MName("#", 1))); var s= ms.getFirst().sig();
        ck(!(ms.getFirst().impl().isPresent() || s.abs() || has(from(s.origin().get()).cs(), baseId))); }
      if (allCs.stream().noneMatch(c -> c.name().equals(sealed))){ return; }
      ck(allCs.stream().anyMatch(c -> !c.name().pkgName().equals(d.name().pkgName()) && has(from(c.name()).cs(), sealed))); } void register(IE.Lit d){
      var ms= d.ms().stream().map(m -> { var s= ToCore.sig(m.sig(), m.sig());
        return new M(s, m.impl().isEmpty() ? Collections.nCopies(s.ts().size(), "_") : m.impl().get().xs(), m.impl().isEmpty() ? Optional.<E>empty() : Optional.<E>of(new E.X("this")));
      }).toList();
      cache.put(d.name(), new Literal(d.rc().orElse(RC.imm), d.name(), d.bs(), d.cs().stream().map(Frontend::normC).toList(), d.thisName(), ms, d.infName())); }
    List<IM> inferMNames(List<IM> ms, ArrayList<ISig> ss){ var res= new ArrayList<IM>(ms.size()); for (var m : ms){ if (m.sig().m().isEmpty()){ continue; }
        ss.removeIf(s -> s.m().get().equals(m.sig().m().get())); res.add(m); } if (res.size() == ms.size()){ return ms; }
      for (var m : ms){ if (m.sig().m().isEmpty()){ res.add(nameFromSigs(m, ss)); } } return List.copyOf(res); } IM nameFromSigs(IM m, ArrayList<ISig> ss){
      var arity= m.sig().ts().size(); for (var abs : List.of(true, false)){
        var match= ss.stream().filter(s -> s.m().get().arity() == arity && (s.abs() || !abs)).toList(); ss.removeAll(match);
        var count= match.stream().map(s -> s.m().get()).distinct().count(); ck(count > 1); if (count == 1){ var s= m.sig();
          return new IM(new ISig(s.rc(), match.getFirst().m(), s.bs(), s.ts(), s.ret(), s.origin(), s.abs(), s.span()), m.impl()); } } throw new Fail(); }
    List<IM> pairWithSig(List<IM> ms, ArrayList<ISig> ss, IE.Lit origin){ var res= new ArrayList<IM>(); var changed= false; for (var m : ms){
        var name= m.sig().m().get(); var rc= m.sig().rc();
        var taken= ss.stream().filter(s -> s.m().get().equals(name) && (rc.isEmpty() || rc.equals(s.rc()))).toList(); ss.removeAll(taken);
        var match= taken.stream().collect(Collectors.groupingBy(s -> s.rc().get(), LinkedHashMap::new, Collectors.toList()));
        if (rc.isEmpty() && match.size() > 1 && InjectionSteps.noH(origin.rc().or(origin.t()::explicitRC).orElse(RC.imm)).isReadOrImm()){
          var dead= match.remove(RC.mut); if (dead != null){ ss.addAll(dead); } }
        List<List<ISig>> groups= match.isEmpty() ? List.of(List.of()) : List.copyOf(match.values()); var first= true; for (var matches : groups){
          var mi= first ? m : dupM(fresh, m, origin.name(), origin.name()); first = false;
          var m2= pairWithSig(Collections.unmodifiableList(matches), mi, origin); changed |= m2 != mi; res.add(m2); } } if (!ss.isEmpty()){ changed = true;
        ss.stream().collect(Collectors.groupingBy(s -> new RCMName(s.rc(), s.m().get()), LinkedHashMap::new, Collectors.toList())).values().forEach(v -> res.add(pairWithSig(v, origin)));
      } return changed ? List.copyOf(res) : ms; } IM pairWithSig(List<ISig> ss, IM m, IE.Lit origin){ var s= m.sig(); if (ss.isEmpty()){
        var ts= s.ts().stream().map(t -> Optional.of(t.orElseThrow(Fail::new))).toList();
        return m.withSig(new ISig(s.rc().orElse(RC.imm), s.m().get(), s.bs().orElse(List.of()), ts, s.ret().orElseThrow(Fail::new), origin.name(), m.impl().isEmpty(), s.span()));
      } var allBounds= ss.stream().map(e -> e.bs().get()).distinct().toList(); List<B> bs; if (s.bs().isEmpty()){ bs = agreementBs(allBounds); } else{
        var userBs= s.bs().get(); var superArities= ss.stream().map(e -> e.bs().get().size()).distinct().toList();
        ck(superArities.size() != 1 || superArities.getFirst() != userBs.size());
        ck(!agreementBs(allBounds).stream().map(B::rcs).toList().equals(userBs.stream().map(B::rcs).toList())); bs = userBs; }
      var ssAligned= alignMethodSigsTo(ss, bs);
      var ts= IntStream.range(0, s.ts().size()).mapToObj(i -> Optional.of(s.ts().get(i).orElseGet(() -> agreement(origin, ssAligned, e -> e.ts().get(i).get())))).toList();
      var res= s.ret().orElseGet(() -> agreement(origin, ssAligned, e -> e.ret().get())); var rc= s.rc().orElseGet(() -> ssAligned.getFirst().rc().get());
      return m.withSig(new ISig(rc, ssAligned.getFirst().m().get(), bs, ts, res, origin.name(), m.impl().isEmpty(), s.span())); }
    IM pairWithSig(List<ISig> ss, IE.Lit origin){ if (ss.size() == 1){ return new IM(ss.getFirst(), Optional.empty()); }
      var bs= agreementBs(ss.stream().map(e -> e.bs().get()).distinct().toList()); var ssAligned= alignMethodSigsTo(ss, bs);
      var name= ssAligned.getFirst().m().get();
      var ts= IntStream.range(0, name.arity()).mapToObj(i -> Optional.of(agreement(origin, ssAligned, e -> e.ts().get(i).get()))).toList();
      var res= agreement(origin, ssAligned, e -> e.ret().get());
      var impl= ssAligned.stream().filter(e -> !e.abs() && !overridden(e, origin)).map(e -> e.origin().get()).distinct().toList(); ck(impl.size() > 1);
      return new IM(new ISig(ssAligned.getFirst().rc().get(), name, bs, ts, res, impl.size() == 1 ? impl.getFirst() : origin.name(), impl.isEmpty(), ssAligned.getFirst().span()), Optional.empty());
    } boolean overridden(ISig s, IE.Lit lit){ var sup= s.origin().get(); return lit.cs().stream()
        .flatMap(c -> Stream.concat(Stream.of(c.name()), from(c.name()).cs().stream().map(IT.C::name))) .anyMatch(t -> { var d= from(t);
          return !t.equals(sup) && has(d.cs(), sup) && d.ms().stream().map(M::sig).anyMatch(o -> o.origin().equals(d.name()) && o.m().equals(s.m().get()) && o.rc() == s.rc().get());
        }); } IT agreement(IE.Lit lit, List<ISig> ss, Function<ISig,IT> f){ var res= ss.stream().map(f).distinct().toList();
      var bs= push(lit.bs(), ss.getFirst().bs().get()); var first= norm(res.getFirst());
      if (res.stream().allMatch(t -> TypeSystem.eqModXRC(bs, first, norm(t)))){ return res.getFirst(); } throw new Fail(); }
    List<B> agreementBs(List<List<B>> res){
      ck(res.stream().map(List::size).distinct().count() != 1 || res.stream().map(l -> l.stream().map(B::rcs).toList()).distinct().count() != 1);
      return res.getFirst(); } List<ISig> alignMethodSigsTo(List<ISig> ss, List<B> targetBs){ return ss.stream().map(superSig -> {
        var fromXs= B.xs(superSig.bs().get()); var toITs= toXs(B.xs(targetBs));
        var renamedTs= superSig.ts().stream().map(t -> Optional.of(rename(t.get(), fromXs, toITs))).toList();
        return new ISig(superSig.rc(), superSig.m(), Optional.of(targetBs), renamedTs, superSig.ret().map(it -> rename(it, fromXs, toITs)), superSig.origin(), superSig.abs(), superSig.span());
      }).toList(); } } record InjectionSteps(Methods meths){ static List<Literal> steps(Methods meths, List<IE.Lit> tops){ var s= new InjectionSteps(meths);
      return tops.stream().map(l -> { var di= meths.cache.get(l.name()); return di.withMs(l.ms().stream().map(m -> s.stepDecM(di, m)).toList()); }).toList(); }
    M stepDecM(Literal di, IM m){
      var mCore= di.ms().stream().filter(mi -> mi.sig().m().equals(m.sig().m().get()) && mi.sig().rc() == m.sig().rc().orElse(RC.imm)).findFirst().get();
      if (m.impl().isEmpty()){ return mCore; } var e= m.impl().get().e(); var xs= m.impl().get().xs(); var ei= meet(e, mCore.sig().ret()); var g= new IGamma();
      for (int i= 0; i < xs.size(); i++){ g.declare(xs.get(i), mCore.sig().ts().get(i)); }
      g.declare(di.thisName(), new IT.RCC(Optional.of(mCore.sig().rc()), new IT.C(di.name(), toXs(B.xs(di.bs()))))); var bs= push(di.bs(), m.sig().bs().get());
      ei = nextStar(bs, g, ei); return new M(mCore.sig(), xs, Optional.of(new ToCore(bs).of(ei, e))); } IE meet(IE e, IT t){
      if (e instanceof IE.Type tt){ return nextT(tt); } if (e instanceof IE.Lit l && l.t().isTV()){ return e; } e = prototypeAscribeRootReceiver(e, t, false);
      return e.withT(meet(e.t(), t)); } IT leastBad(IT.RCC a, IT.RCC b){ var aSuper= isASuperB(a.c().name(), b.c().name());
      var bSuper= isASuperB(b.c().name(), a.c().name());
      var aBad= bSuper ? Math.max(adaptedSuperTs(a, b.c().name()).getFirst().badness(), a.badness()) : a.badness();
      var bBad= aSuper ? Math.max(adaptedSuperTs(b, a.c().name()).getFirst().badness(), b.badness()) : b.badness();
      if (aBad != bBad){ return aBad < bBad ? a : b; } if (aSuper){ return b; } if (bSuper){ return a; }
      if (a.depth() != b.depth()){ return a.depth() < b.depth() ? a : b; } return a.c().name().s().compareTo(b.c().name().s()) < 0 ? a : b; }
    IT leastBad(IT a, IT b){ if (a instanceof IT.RCC){ return a; } if (b instanceof IT.RCC){ return b; }
      if (a instanceof IT.RCX && (b instanceof IT.X || b instanceof IT.ReadImmX)){ return a; }
      if (b instanceof IT.RCX && (a instanceof IT.X || a instanceof IT.ReadImmX)){ return b; } return a.toString().compareTo(b.toString()) < 0 ? a : b; }
    IT meet(IT t1, IT t2){ if (t2 instanceof IT.U){ return t1; } if (t1 instanceof IT.U || t1.equals(t2)){ return t1 instanceof IT.U ? t2 : t1; }
      if (t1 instanceof IT.ReadImmX(var x1) && x1.equals(t2)){ return t1; } if (t2 instanceof IT.ReadImmX(var x2) && x2.equals(t1)){ return t2; }
      if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){ if (!x1.c().name().equals(x2.c().name())){ return leastBad(x1, x2); }
        return x1.withRCTs(meetRcNoH(x1.rc(), x2.rc()), meet(x1.c().ts(), x2.c().ts())); }
      if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX(var rc2, var x2)) || !x1.x().equals(x2)){ return leastBad(t1, t2); }
      return x1.withRC(meetRcNoH(Optional.of(x1.rc()), Optional.of(rc2)).get()); } static Optional<RC> meetRcNoH(Optional<RC> a, Optional<RC> b){
      if (a.isEmpty()){ return b; } if (b.isEmpty()){ return a; } var x= noH(a.get()); var y= noH(b.get());
      if (x == y || y == RC.iso || y == RC.read && x != RC.iso){ return Optional.of(x); } if (x == RC.iso || x == RC.read){ return Optional.of(y); }
      return Optional.of(RC.imm); } static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
    List<IT> meet(List<IT> t1, List<IT> t2){ return zip(t1, t2, this::meet).toList(); }
    List<IT> meet(List<List<IT>> tss){ return tss.stream().reduce(this::meet).get(); } IE nextStar(List<B> bs, IGamma g, IE e){
      if (g.snap().equals(e.g().snap)){ return e; } while (true){ var s= g.snap(); var oe= next(bs, g, e);
        if (oe == e && s.equals(g.snap())){ e.g().snap = s; return e; } e = oe; } }
    List<IE> nextStar(List<B> bs, IGamma g, List<IE> es){ return norm(es, es.stream().map(ei -> nextStar(bs, g, ei)).toList()); }
    List<IE> meetWithTargs(List<IE> es, MSigL m, List<IT> targs){ return norm(es, zip(es, m.ps0(), (e,p) -> meet(e, m.inst(p, targs))).toList()); }
    IE next(List<B> bs, IGamma g, IE e){ return switch (e){ case IE.X x -> { var t1Base= g.get(x.name()); ck(g.notFunnelledInto(x.name()));
          var t1= g.getWithRC(x.name()); var t2= x.t(); if (t1.equals(t2)){ yield x; } if (!(t2 instanceof IT.U)){ updateG(g, x.name(), t1Base, t2); }
          yield x.withT(meet(t1, t2)); } case IE.Lit l -> nextL(bs, g, l); case IE.Call c -> nextC(bs, g, c); case IE.ICall c -> {
          var ee= nextStar(bs, g, c.e()); var es= nextStar(bs, g, c.es()); if (!(ee.t() instanceof IT.RCC rcc)){ yield c.withEEs(ee, es); }
          var om= methodHeader(rcc, c.name(), Optional.empty()); if (om.isEmpty()){ yield c.withEEs(ee, es); } var m= om.get();
          var ts= qMarks(m.methBs().size());
          yield new IE.Call(ee, c.name(), Optional.of(m.rc()), ts, meetWithTargs(es, m, ts), false).withT(meet(c.t(), m.inst(m.ret0(), ts))); }
        case IE.Type c -> nextT(c); }; } IT preferred(IT.RCC type){ var d= meths.from(type.c().name());
      var c= d.cs().stream().filter(ci -> ci.name().equals(widen)).findFirst(); if (c.isEmpty()){ return type; }
      var wid= rename(c.get().ts().getFirst(), B.xs(d.bs()), type.c().ts()); if (!(wid instanceof IT.RCC(_, var widC))){ return type; }
      return new IT.RCC(type.rc(), widC); } <R> Optional<R> methodHeaderAnd(IT.RCC rcc, MName name, Optional<RC> favorite, BiFunction<Literal,M,R> f){
      var d= meths.from(rcc.c().name()); if (d == null){ return Optional.empty(); } var ms= d.ms().stream().filter(m -> m.sig().m().equals(name)).toList();
      Function<RC,Optional<M>> one= rc -> ms.stream().filter(m -> m.sig().rc() == rc).findFirst();
      var rc= rcc.rc().map(r -> r == RC.iso ? RC.imm : noH(r)).orElse(RC.imm);
      var om= favorite.map(one).orElseGet(() -> ms.size() == 1 ? Optional.of(ms.getFirst())
        : rc == RC.read ? one.apply(RC.read).or(() -> one.apply(RC.imm)).or(() -> one.apply(RC.mut))
        : rc == RC.mut ? one.apply(RC.mut).or(() -> one.apply(RC.read)).or(() -> one.apply(RC.imm))
        : one.apply(RC.imm).or(() -> one.apply(RC.read)).or(() -> one.apply(RC.mut))); return om.map(mm -> f.apply(d, mm)); }
    Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){
      return methodHeaderAnd(rcc, name, favorite, (d,m) -> new MSigL(m.sig().rc(), push(B.xs(d.bs()), B.xs(m.sig().bs())), d.bs(), rcc.c().ts(), m.sig().bs(), m.sig().ts(), m.sig().ret()));
    } static List<IT> qMarksAt(int n, IT t, int tot){ return IntStream.range(0, tot).<IT>mapToObj(i -> i == n ? t : IT.U.Instance).toList(); }
    static void updateG(IGamma g, String x, IT t1, IT t2){ var t= t1 instanceof IT.U ? t2
        : t1 instanceof IT.RCC(var aRc, var aC) && t2 instanceof IT.RCC(var bRc, var bC) && aC.name().equals(bC.name()) ? new IT.RCC(aRc.isEmpty() ? bRc : bRc.isEmpty() ? aRc : Optional.of(glbRcNoH(aRc.get(), bRc.get())), aC)
        : t1 instanceof IT.RCX a && t2 instanceof IT.RCX(var bRc, var bX) && a.x().equals(bX) ? a.withRC(glbRcNoH(a.rc(), bRc)) : null;
      if (t != null){ g.fs.get(g.at(x)).vars().put(x, t); } } static RC glbRcNoH(RC a, RC b){ a = noH(a); b = noH(b);
      return a == b || b == RC.read ? a : a == RC.read ? b : RC.iso; } IE nextT(IE.Type t){ return t.t() instanceof IT.U ? t.withT(preferred(t.type())) : t; }
    IE nextC(List<B> bs, IGamma g, IE.Call c){ var e= nextStar(bs, g, c.e());
      if (!(e.t() instanceof IT.RCC rcc)){ return c.withEEs(e, nextStar(bs, g, c.es())); } var om= methodHeader(rcc, c.name(), c.rc());
      if (om.isEmpty()){ return c.withEEs(e, nextStar(bs, g, c.es())); } var m= om.get(); var nCls= m.clsArgs().size();
      var all0= decidedThen(c, m, c.es(), Stream.of()); var m0= m.withClsArgs(normToBounds(bs, m.clsBs(), all0.subList(0, nCls)));
      var es= nextStar(bs, g, meetWithTargs(c.es(), m0, normToBounds(bs, m.methBs(), all0.subList(nCls, all0.size()))));
      var all= decidedThen(c, m, es, zip(m.ps0(), es, (p,e2) -> refine(m.xs(), p, e2.t()))); var clsTs= normToBounds(bs, m.clsBs(), all.subList(0, nCls));
      var targs= normToBounds(bs, m.methBs(), all.subList(nCls, all.size())); e = meet(e, rcc.withTs(clsTs)); var m1= m.withClsArgs(clsTs);
      var it= meet(c.t(), m1.inst(m1.ret0(), targs)); var es1= meetWithTargs(es, m1, targs);
      if (e == c.e() && es1 == c.es() && targs.equals(c.targs()) && it.equals(c.t())){ return c; } return c.withMore(e, c.rc().orElse(m1.rc()), targs, es1, it);
    } List<IT> decidedThen(IE.Call c, MSigL m, List<IE> es, Stream<List<IT>> argRefinements){ var targs= MSigL.fixTargs(c.targs(), m.methBs().size());
      var all= meet(cat(Stream.of(push(m.clsArgs(), targs)), argRefinements, Stream.of(refine(m.xs(), m.ret0(), c.t()))).toList());
      var written= push(m.clsArgs(), c.written() ? targs : qMarks(m.methBs().size()));
      var fromLiterals= IntStream.range(0, es.size()).filter(i -> es.get(i) instanceof IE.Lit).mapToObj(i -> refine(m.xs(), m.ps0().get(i), es.get(i).t()));
      var hard= meet(Stream.concat(Stream.of(qMarks(written.size())), fromLiterals).toList());
      var fixed= zip(written, hard, (w,h) -> decided(w) ? w : h).toList(); return zip(fixed, all, (b,r) -> decided(b) ? b : r).toList(); }
    static boolean decided(IT t){ return t.isTV() && !(t instanceof IT.RCC(var rc, _) && rc.isEmpty()); } Optional<IT.RCC> preciseSelf(IE.Lit l){
      if (l.infName() && l.rc().isEmpty()){ return Optional.empty(); } return Optional.of(new IT.RCC(l.rc(), new IT.C(l.name(), toXs(B.xs(l.bs()))))); }
    IE nextL(List<B> bs, IGamma g, IE.Lit l){ var selfPrecise= preciseSelf(l); if (!l.infHead()){ var cs0= l.cs();
        var selfSuper= cs0.size() != 1 ? selfPrecise : selfPrecise.map(p -> new IT.RCC(p.rc(), cs0.getFirst()));
        l = l.infName() ? selfSuper.map(l::withT).orElse(l) : l.withT(selfPrecise.get()); if (!(l.t() instanceof IT.RCC(_, var c))){ return l; }
        l = l.infName() && !c.name().equals(l.name()) ? meths.expandLiteral(l, c, bs) : meths.expandDeclaration(l, true); }
      if (!(l.t() instanceof IT.RCC rcc)){ return l; } var res= new ArrayList<IM>(l.ms().size()); var ts= rcc.c().ts(); for (var mi : l.ms()){
        var rcci= withTsNormBs(rcc, ts); var next= mi.impl().isEmpty() ? nextMStarAbs(rcci, mi) : nextMStarOp(bs, g, l, selfPrecise, rcci, mi);
        ts = meet(ts, next.ts); res.add(next.m); } var ms= norm(l.ms(), Collections.unmodifiableList(res));
      if (ms == l.ms() && ts.equals(rcc.c().ts())){ return commitToTable(g, bs, l, rcc); } var t= withTsNormBs(rcc, ts);
      return commitToTable(g, bs, l.withMsT(ms, t), t); } IE commitToTable(IGamma g, List<B> bs, IE.Lit l, IT.RCC rcc){ var name= l.name();
      if (!rcc.isTV() || !l.ms().stream().allMatch(m -> m.sig().ret().get().isTV() && m.sig().ts().stream().allMatch(t -> t.get().isTV())) || meths.cache.containsKey(name)){ return l; }
      var localBs= cat(ftvMs(g, l.ms()), ftvCs(l.cs()), rcc.ftv()).distinct().map(x -> B.get(bs, x)).toList(); var newName= name.withArity(localBs.size());
      var ms= name.equals(newName) ? l.ms() : norm(l.ms(), l.ms().stream().map(mi -> !mi.sig().origin().get().equals(name) ? mi : mi.withSig(mi.sig().withOrigin(newName))).toList());
      var orc= l.rc().or(rcc::rc).map(InjectionSteps::noH); var orcc= new IT.RCC(orc, rcc.c());
      if (l.ms().stream().allMatch(m -> m.impl().isEmpty()) && l.infHead() && meths.from(rcc.c().name()) != null){ return new IE.Type(orcc, preferred(orcc), l.g()); }
      var selfInferred= rcc.c().name().equals(l.name());
      var cs= ToCore.distinctTypes(localBs, selfInferred ? meths.fetchCs(rcc.c()) : push(rcc.c(), meths.fetchCs(rcc.c()))); meths.checkMagicSupertypes(l, cs);
      l = new IE.Lit(orc, newName, localBs, cs, l.thisName(), ms, rcc, l.bsWritten(), l.infName(), l.infHead(), l.g());
      if (selfInferred){ l = l.withT(preciseSelf(l).get()); } meths.register(l); return l; } record TSM(List<IT> ts, IM m){} TSM nextMStarAbs(IT.RCC rcc, IM m){
      var omh= methodHeaderAnd(rcc, m.sig().m().get(), m.sig().rc(), (_,mi) -> mi); if (omh.isEmpty()){ return new TSM(rcc.c().ts(), m); }
      var rcc0= withTsNormBs(rcc, refineClsTsFromHeader(rcc, m.sig(), omh.get().sig()));
      return new TSM(dropMethBs(rcc0.c().ts(), B.xs(m.sig().bs().get())), m.withSig(normalizeSigAgainstHeader(rcc0, m.sig()))); }
    TSM nextMStarOp(List<B> bs, IGamma g, IE.Lit l, Optional<IT.RCC> selfPrecise, IT.RCC rcc, IM m){ var litBs= l.infName() ? bs : l.bs();
      var impl= m.impl().get(); g.fs.add(new IGamma.Frame(m.sig().rc().get(), litBs, new LinkedHashMap<>()));
      g.declare(l.thisName(), selfPrecise.<IT>map(s -> new IT.RCC(s.rc().map(RC::isoToMut), s.c())).orElse(IT.U.Instance));
      g.fs.add(new IGamma.Frame(m.sig().rc().get(), litBs, new LinkedHashMap<>()));
      for (int i= 0; i < impl.xs().size(); i++){ g.declare(impl.xs().get(i), m.sig().ts().get(i).get()); }
      var e= nextStar(push(litBs, m.sig().bs().get()), g, meet(impl.e(), m.sig().ret().get()));
      var args= zip(impl.xs(), m.sig().ts(), (x,oi) -> x.equals("_") ? oi : Optional.of(meet(oi.get(), g.get(x)))).toList(); g.fs.removeLast();
      g.fs.removeLast(); var improvedSig= m.sig().withTsT(args, meet(m.sig().ret().get(), e.t()));
      var omh= methodHeaderAnd(rcc, improvedSig.m().get(), improvedSig.rc(), (_,mi) -> mi);
      if (omh.isEmpty()){ return withImpl(rcc.c().ts(), m, improvedSig, e); }
      var rcc0= withTsNormBs(rcc, refineClsTsFromHeader(rcc, improvedSig, omh.get().sig()));
      return withImpl(dropMethBs(rcc0.c().ts(), B.xs(improvedSig.bs().get())), m, normalizeSigAgainstHeader(rcc0, improvedSig), e); }
    TSM withImpl(List<IT> ts, IM m, ISig sig, IE e){ var impl1= m.impl().get().withE(meet(e, sig.ret().get()));
      if (sig.equals(m.sig()) && impl1 == m.impl().get()){ return new TSM(ts, m); } return new TSM(ts, new IM(sig, Optional.of(impl1))); }
    List<IT> refineClsTsFromHeader(IT.RCC rcc, ISig improvedSig, Sig imh){ var Xs= B.xs(meths.from(rcc.c().name()).bs());
      var fromBody= meet(Stream.concat(zip(imh.ts(), improvedSig.ts(), (t,it) -> refine(Xs, t, it.get())), Stream.of(refine(Xs, imh.ret(), improvedSig.ret().get()))).toList());
      return zip(rcc.c().ts(), fromBody, this::keepDecided).toList(); } IT keepDecided(IT decided, IT fromBody){
      var decidedIso= decided instanceof IT.RCX(var aRc, _) && aRc == RC.iso;
      if (xName(decided).isPresent() && xName(decided).equals(xName(fromBody)) && !decidedIso){ return decided; }
      if (!(decided instanceof IT.RCC(var aRc, var aC) && fromBody instanceof IT.RCC b)){ return meet(decided, fromBody); }
      if (!aC.name().equals(b.c().name())){ var asDecided= adaptedSuperTs(b, aC.name());
        return asDecided.isEmpty() ? decided : keepDecided(decided, asDecided.getFirst()); }
      return b.withRCTs(aRc.or(b::rc), zip(aC.ts(), b.c().ts(), this::keepDecided).toList()); } ISig normalizeSigAgainstHeader(IT.RCC rcc, ISig improvedSig){
      var h= methodHeader(rcc, improvedSig.m().get(), improvedSig.rc()).get(); var xs= toXs(B.xs(improvedSig.bs().get()));
      return improvedSig.withTsT(h.ps0().stream().map(p -> Optional.of(h.inst(p, xs))).toList(), h.inst(h.ret0(), xs)); }
    List<IT> dropMethBs(List<IT> ts, List<String> methBs){ if (methBs.isEmpty()){ return ts; }
      return ts.stream().map(t -> t instanceof IT.RCC rcc ? withTsNormBs(rcc, dropMethBs(rcc.c().ts(), methBs)) : xName(t).filter(methBs::contains).isPresent() ? IT.U.Instance : t).toList();
    } List<IT> refine(List<String> xs, IT t, IT t1){ if (t1 instanceof IT.U){ return qMarks(xs.size()); } return switch (t){
        case IT.X x -> qMarksAt(xs.indexOf(x.name()), t1, xs.size()); case IT.RCX(_, var x) -> refine(xs, x, switch (t1){ case IT.RCX(_, var x1) -> x1;
          case IT.ReadImmX(var x1) -> x1; case IT.RCC(_, var c) -> new IT.RCC(Optional.empty(), c); default -> t1; });
        case IT.ReadImmX(var x) -> refine(xs, x, t1 instanceof IT.ReadImmX(var x1) ? x1 : t1); case IT.RCC rcc -> propagateXs(xs, rcc, t1);
        case IT.U _ -> qMarks(xs.size()); }; } boolean isASuperB(TName a, TName b){ var d= meths.from(b); return d != null && has(d.cs(), a); }
    List<IT.RCC> adaptedSuperTs(IT.RCC src, TName target){ var d= meths.from(src.c().name()); if (d == null){ return List.of(); }
      return d.cs().stream().filter(sc -> sc.name().equals(target)).distinct()
        .map(ci -> (IT.RCC)rename(new IT.RCC(src.rc(), ci), B.xs(d.bs()), src.c().ts())).toList(); } List<IT> propagateXs(List<String> xs, IT.RCC r, IT t1){
      if (!(t1 instanceof IT.RCC cc)){ return qMarks(xs.size()); } var c= r.c(); if (!cc.c().name().equals(c.name())){ var supOk= adaptedSuperTs(cc, c.name());
        if (!supOk.isEmpty()){ return propagateXs(xs, r, supOk.getFirst()); } var subOk= adaptedSuperTs(r, cc.c().name());
        if (!subOk.isEmpty()){ return propagateXs(xs, subOk.getFirst(), t1); } return qMarks(xs.size()); }
      var res= zip(c.ts(), cc.c().ts(), (t,ti) -> t instanceof IT.RCC rr && !(ti instanceof IT.RCC ci && ci.c().name().equals(rr.c().name())) ? qMarks(xs.size()) : refine(xs, t, ti)).toList();
      return res.isEmpty() ? qMarks(xs.size()) : meet(res); } static <TT> List<TT> norm(List<TT> original, List<TT> candidate){
      if (candidate == original){ return original; } for (int i= 0; i < original.size(); i++){ if (candidate.get(i) != original.get(i)){ return candidate; } }
      return original; } IE prototypeAscribeRootReceiver(IE arg, IT expected, boolean receiver){ if (!(expected instanceof IT.RCC exp)){ return arg; }
      return switch (arg){ case IE.Call c -> c.withEEs(prototypeAscribeRootReceiver(c.e(), expected, true), c.es());
        case IE.ICall c -> c.withEEs(prototypeAscribeRootReceiver(c.e(), expected, true), c.es());
        case IE.Lit l when l.infHead() || !l.infName() || !l.cs().isEmpty() || !(l.t() instanceof IT.U) -> arg;
        case IE.Lit l when !receiver || implementable(exp.c().name()) -> l.withT(new IT.RCC(exp.rc(), new IT.C(exp.c().name(), qMarks(exp.c().ts().size()))));
        case IE.Lit l -> { var res= new IE.Lit(Optional.of(RC.imm), l.name(), l.bs(), l.cs(), l.thisName(), l.ms(), l.bsWritten(), true);
          yield res.withT(preciseSelf(res).get()); } default -> arg; }; } boolean implementable(TName head){ var d= meths.from(head);
      if (d == null){ return false; } var foreignForbidden= !head.pkgName().equals(meths.p.name()) && (!head.isPublic() || has(d.cs(), sealed));
      return !foreignForbidden && TypeSystem.hasInstance(d); } static IT normToBound(IT t, EnumSet<RC> allowed){
      if (allowed.size() == 1){ return t.withRC(allowed.iterator().next()); } if (!(t instanceof IT.RCC(var rc, var c))){ return t; }
      if (!(rc.isEmpty() || rc.get() == RC.iso && !allowed.contains(RC.iso))){ return t; }
      return new IT.RCC(allowed.contains(RC.imm) ? Optional.empty() : Optional.of(RC.read), c); }
    static List<IT> normToBounds(List<B> scope, List<B> bs, List<IT> ts){
      return zip(ts, bs, (ti,bi) -> xName(ti).map(x -> B.get(scope, x).rcs().equals(bi.rcs())).orElse(true) ? normToBound(ti, bi.rcs()) : ti).toList(); }
    static Optional<String> xName(IT t){ return switch (t){ case IT.X x -> Optional.of(x.name()); case IT.RCX(_, var x) -> Optional.of(x.name());
      case IT.ReadImmX(var x) -> Optional.of(x.name()); default -> Optional.empty(); };} IT.RCC withTsNormBs(IT.RCC rcc, List<IT> ts){
      var d= meths.from(rcc.c().name()); return d == null ? rcc.withTs(ts) : rcc.withTs(zip(ts, d.bs(), (ti,bi) -> normToBound(ti, bi.rcs())).toList()); } }
  record ToCore(List<B> ctx){ E of(IE exp, IE orig){ return switch (exp){ case IE.X(var name, _, _) -> new E.X(name);
      case IE.Type(var type, _, _) -> new E.Type((IT.RCC)norm(type)); case IE.Lit le -> literal(le, (IE.Lit)orig); case IE.Call e -> {
        var o= callLike(orig, e.name());
        yield new E.Call(of(e.e(), o.e()), e.name(), o.rc().or(e::rc).orElse(RC.imm), (o.targs().isEmpty() ? e.targs() : o.targs()).stream().map(Frontend::norm).toList(), zip(e.es(), o.es(), this::of).toList(), new H<>(norm(e.t())));
      } case IE.ICall e -> { var o= callLike(orig, e.name());
        yield new E.Call(of(e.e(), o.e()), e.name(), RC.imm, List.of(), zip(e.es(), o.es(), this::of).toList(), new H<>(norm(e.t()))); } };}
    static IE.Call callLike(IE o, MName name){ return switch (o){ case IE.Call c when c.name().equals(name) -> c;
        case IE.ICall c when c.name().equals(name) -> new IE.Call(c.e(), c.name(), Optional.empty(), List.of(), c.es(), false); default -> throw new Fail(); };
    } Literal literal(IE.Lit e, IE.Lit o){ var bs= o.bsWritten() ? o.bs() : e.bs(); if (e.infName() && bs.isEmpty()){ var g= new IGamma();
        bs = cat(ftvCs(e.cs()), ftvMs(g, e.ms()), ftvMs(g, o.ms())).distinct().map(x -> B.get(ctx, x)).toList(); } var name= e.name().withArity(bs.size());
      var inner= new ToCore(e.infName() ? push(ctx, bs).stream().distinct().toList() : bs);
      var ms= e.ms().stream().map(me -> inner.m(me, me.impl().isEmpty() ? me : o.ms().stream().filter(om -> om.sig().span() == me.sig().span()).findFirst().get()))
        .map(m -> !m.sig().origin().equals(e.name()) ? m : m.withSig(new Sig(m.sig().rc(), m.sig().m(), m.sig().bs(), m.sig().ts(), m.sig().ret(), name, m.sig().abs()))).toList();
      var cs= distinctTypes(inner.ctx(), o.cs().isEmpty() ? e.cs() : push(o.cs(), e.cs())).stream().map(Frontend::normC).toList();
      return new Literal(o.rc().or(e::rc).orElse(RC.imm), name, bs, cs, e.thisName(), ms, e.infName()); }
    static List<IT.C> distinctTypes(List<B> bs, List<IT.C> cs){ var res= new ArrayList<IT.C>();
      for (var c : cs){ if (res.stream().noneMatch(r -> TypeSystem.eqModXRC(bs, new IT.RCC(Optional.of(RC.imm), normC(r)), new IT.RCC(Optional.of(RC.imm), normC(c))))){ res.add(c); } }
      return Collections.unmodifiableList(res); } M m(IM e, IM o){ var s= sig(e.sig(), o.sig());
      if (e.impl().isEmpty()){ return new M(s, Collections.nCopies(s.ts().size(), "_"), Optional.empty()); }
      return new M(s, e.impl().get().xs(), Optional.of(new ToCore(push(ctx, s.bs()).stream().distinct().toList()).of(e.impl().get().e(), o.impl().get().e())));
    } static Sig sig(ISig inf, ISig usr){ var ts= zip(usr.ts(), inf.ts(), (u,i) -> u.or(() -> i)).toList();
      return new Sig(usr.rc().or(inf::rc).orElse(RC.imm), usr.m().or(inf::m).orElse(new MName(".inferenceFailed", ts.size())), usr.bs().or(inf::bs).orElse(List.of()),
        ts.stream().map(Frontend::norm).toList(), norm(usr.ret().or(inf::ret)), usr.origin().or(inf::origin).orElse(inferUnknown), usr.abs()); } }
  sealed interface Change{ record WithT(IT currentT) implements Change{} enum NoT implements Change{ Instance } }
  record Gamma(Gamma tail, String name, IT t, Change current){ static final Gamma empty= new Gamma(null, null, null, null);
    Gamma add(String name, IT t){ return new Gamma(this, name, t, new Change.WithT(t)); }
    Gamma map(Function<Change,Change> f){ return this == empty ? this : new Gamma(tail.map(f), name, t, f.apply(current)); }
    Change bind(String x){ return this == empty ? null : name.equals(x) ? current : tail.bind(x); }
    Gamma filterFTV(Literal l){ return filterFTV(l, has(l.cs(), captureFree)); } Gamma filterFTV(Literal l, boolean captureFree){
      if (this == empty){ return this; } var rest= tail.filterFTV(l, captureFree);
      var drop= captureFree || current instanceof Change.WithT w && !hasOnlyFTV(w.currentT(), l.bs());
      return new Gamma(rest, name, t, drop ? Change.NoT.Instance : current); } static boolean hasOnlyFTV(IT t, List<B> bs){ return switch (t){
      case IT.X(var x) -> B.xs(bs).contains(x); case IT.RCX(_, var x) -> hasOnlyFTV(x, bs); case IT.ReadImmX(var x) -> hasOnlyFTV(x, bs);
      case IT.RCC(_, var c) -> c.ts().stream().allMatch(ti -> hasOnlyFTV(ti, bs)); case IT.U _ -> true; };} } record Reason(IT best, boolean isEmpty){}
  record MType(RC rc, List<IT> ts, IT t){} enum Mode{
    useRead(iso, readH, mutH, readH), flexy(iso, imm, mutH, readH), hyg(mutH, readH, mutH, readH), strong(iso, imm, iso, imm); final RC m, r, mh, rh;
    Mode(RC m, RC r, RC mh, RC rh){ this.m= m; this.r= r; this.mh= mh; this.rh= rh; }
    RC of(RC rc){ return switch (rc){ case mut -> m; case read -> r; case mutH -> mh; case readH -> rh; default -> rc; }; } }
  record TypeSystem(Function<TName,Literal> decs){ static void allOk(List<Literal> tops, Map<TName,Literal> other){ var map= new HashMap<TName,Literal>();
      tops.forEach(t -> collect(t, map)); var ts= new TypeSystem(n -> from(n, map::get, other)); tops.forEach(l -> ts.litOk(Gamma.empty, l)); }
    static void collect(E e, HashMap<TName,Literal> map){ if (e instanceof Literal l){ map.put(l.name(), l); } e.children().forEach(c -> collect(c, map)); }
    boolean kindOf(List<B> bs, IT t, EnumSet<RC> allowed){ if (!allowed.containsAll(intrinsicRCs(bs, t))){ return false; }
      if (!(t instanceof IT.RCC(_, var c))){ return true; } var params= decs.apply(c.name()).bs();
      return zip(c.ts(), params, (ti,p) -> kindOf(bs, ti, p.rcs())).allMatch(v -> v); } void checkC(List<B> bs, IT.C c){ var params= decs.apply(c.name()).bs();
      for (int i= 0; i < params.size(); i++){ kind(bs, c.ts().get(i), params.get(i).rcs()); } }
    void kind(List<B> bs, IT t){ if (t instanceof IT.RCC rcc){ kind(bs, rcc, EnumSet.allOf(RC.class)); } } void kind(List<B> bs, IT t, EnumSet<RC> allowed){
      if (t instanceof IT.RCC(var rc, var c)){ ck(!allowed.contains(rc.get())); checkC(bs, c); return; } ck(!kindOf(bs, t, allowed)); }
    static EnumSet<RC> intrinsicRCs(List<B> bs, IT t){ return switch (t){ case IT.RCC(var rc, _) -> EnumSet.of(rc.get());
      case IT.RCX(var rc, _) -> EnumSet.of(rc); case IT.X(var x) -> B.get(bs, x).rcs(); case IT.U _ -> throw new Fail(); case IT.ReadImmX(var x) -> {
        var rcs= intrinsicRCs(bs, x);
        yield EnumSet.of(iso, imm).containsAll(rcs) ? EnumSet.of(imm) : EnumSet.of(mut, mutH, read, readH).containsAll(rcs) ? EnumSet.of(read) : EnumSet.of(read, imm);
      } };} boolean kindIsoImm(IT t, List<B> delta){ return kindOf(delta, t, EnumSet.of(iso, imm)); } Gamma vpaOf(Gamma g, Literal l, M m){
      return g.map(current -> { if (!(current instanceof Change.WithT w)){ return current; } var t= w.currentT();
        if (m.sig().rc() == imm || kindIsoImm(t, l.bs())){ return new Change.WithT(t.withRC(imm)); } if (m.sig().rc() == read){
          if (t.explicitRC().stream().anyMatch(r -> r == mut || r == read)){ return new Change.WithT(t.withRC(read)); }
          if (t instanceof IT.X || t instanceof IT.ReadImmX){ return new Change.WithT(t.readImm()); } }
        return kindOf(l.bs(), t, EnumSet.of(imm, mut, read)) ? w : new Change.WithT(t.readImm()); }); } Gamma discard(Gamma g, Literal l){
      return g.map(current -> { if (!(current instanceof Change.WithT w)){ return current; } var t= w.currentT();
        var drop= !kindOf(l.bs(), t, EnumSet.allOf(RC.class)) || !kindOf(l.bs(), t, EnumSet.of(iso, imm, mut, read)) || l.rc().isIsoOrImm() && !kindIsoImm(t, l.bs());
        return drop ? Change.NoT.Instance : w; }); } boolean isSub(List<B> bs, IT t1, IT t2){ return t1.equals(t2)
        || t2 instanceof IT.ReadImmX(var x2) && t1 instanceof IT.X x && x2.name().equals(x.name()) && kindOf(bs, x, EnumSet.of(iso, imm, mut, read))
        || isSameShapeSubtype(bs, t1, t2)
        || t1 instanceof IT.RCC(var rc1, var c1) && decs.apply(c1.name()).cs().stream().anyMatch(ci -> isSub(bs, renameT(new IT.RCC(rc1, ci), B.xs(decs.apply(c1.name()).bs()), c1.ts()), t2));
    } void check(List<B> bs, Gamma g, E e, IT expected){ if (!typeOf(bs, g, e, List.of(expected)).getFirst().isEmpty()){ throw new Fail(); } }
    List<Reason> typeOf(List<B> bs, Gamma g, E e, List<IT> rs){ return switch (e){ case E.X x -> {
        if (!(g.bind(x.name()) instanceof Change.WithT w)){ throw new Fail(); } yield reqs(bs, w.currentT(), rs, false); } case E.Type t -> {
        kind(bs, t.type()); var ll= decs.apply(t.type().c().name()); ck(!hasInstance(ll)); var rc= t.type().rc().get();
        var getIso= (rc.isReadOrImm() && !hasAbstractMut(ll)) || rc == mut || rc == mutH; var l= ll.withRC(getIso ? iso : rc);
        l.ms().forEach(m -> checkImplemented(l, m)); yield reqs(bs, getIso ? t.type().withRC(iso) : t.type(), rs, true); }
      case Literal l -> checkLiteral(bs, g, l, rs); case E.Call c -> callTyping(bs, g, c, rs); };}
    static boolean hasInstance(Literal l){ return l.thisName().equals("this") || has(l.cs(), captureFree); }
    static boolean uses(E e, String x){ return e instanceof E.X(var n) ? n.equals(x) : e.children().anyMatch(ei -> uses(ei, x)); }
    static boolean hasAbstractMut(Literal l){ return l.ms().stream().anyMatch(m -> m.sig().abs() && m.sig().rc() == mut); }
    List<Reason> reqs(List<B> bs, IT got, List<IT> rs, boolean rccOnly){ if (rs.isEmpty()){ return List.of(new Reason(got, true)); }
      ck(rccOnly && rs.stream().anyMatch(r -> !(r instanceof IT.RCC))); return rs.stream().map(r -> new Reason(got, isSub(bs, got, r))).toList(); }
    List<Reason> checkLiteral(List<B> bs1, Gamma g, Literal _l, List<IT> rs){ var selfNamed= !_l.thisName().equals("_");
      var getIso= ((_l.rc().isReadOrImm() && !hasAbstractMut(_l) && !selfNamed) || _l.rc() == mut) && captureFree(_l.bs(), g.filterFTV(_l), RC::isIsoOrImm, _l);
      _l.onlyImmCapture().inner = captureFree(bs1, g, rc -> rc == imm, _l); var l= getIso ? _l.withRC(iso) : _l;
      ck(rs.stream().anyMatch(r -> !(r instanceof IT.RCC)));
      ck(l.ms().stream().anyMatch(m -> m.sig().origin().equals(inferUnknown)) || l.cs().stream().anyMatch(c -> c.ts().stream().anyMatch(TypeSystem::mentionsInferUnknown)));
      var thisType= new IT.RCC(of(l.rc()), new IT.C(l.name(), dom(l.bs()))); kind(bs1, thisType); litOk(discard(g.filterFTV(l), l), l);
      ck(selfNamed && !uses(_l, _l.thisName())); ck(l.ms().stream().anyMatch(m -> m.e().isPresent() && !hasInstance(l) && !callable(l.rc(), m.sig().rc())));
      l.ms().forEach(m -> checkImplemented(l, m)); return reqs(bs1, thisType, rs, false); }
    static boolean captureFree(List<B> bs, Gamma g, Predicate<RC> freeRC, E e){ return switch (e){
        case Literal l -> l.ms().stream().allMatch(m -> m.e().stream().allMatch(b -> captureFree(bs, g, freeRC, b)));
        case E.Call _, E.Type _ -> e.children().allMatch(c -> captureFree(bs, g, freeRC, c));
        case E.X x -> !(g.bind(x.name()) instanceof Change.WithT w) || captureFreeT(bs, freeRC, w.currentT()); }; }
    static boolean captureFreeT(List<B> bs, Predicate<RC> freeRC, IT t){ return switch (t){
        case IT.X(var name) -> B.get(bs, name).rcs().stream().allMatch(freeRC); case IT.RCX(var rc, _) -> freeRC.test(rc);
        case IT.ReadImmX(var x) -> captureFreeT(bs, freeRC, x); case IT.RCC(var rc, _) -> freeRC.test(rc.get()); case IT.U _ -> true; }; }
    static boolean mentionsInferUnknown(IT t){ return t instanceof IT.RCC(_, var c) && (c.name().equals(inferUnknown) || c.ts().stream().anyMatch(TypeSystem::mentionsInferUnknown)); }
    void checkImplemented(Literal l, M m){ if (m.sig().abs() && callable(l.rc(), m.sig().rc())){ throw new Fail(); } }
    static boolean callable(RC litRC, RC recRc){ return recRc != mut || !litRC.isReadOrImm(); } record Key(MName m, RC rc){} void litOk(Gamma g, Literal l){
      if (has(l.cs(), baseId)){ var m= l.ms().getFirst(); var isId= switch (m.e().orElse(null)){ case null -> true;
          case E.X(var name) -> name.equals(m.xs().getFirst());
          case E.Call c -> c.e() instanceof E.X(var recv) && recv.equals(m.xs().getFirst()) && c.name().equals(new MName(".as", 1))
            && m.sig().ts().getFirst() instanceof IT.RCC(_, var cc) && has(decs.apply(cc.name()).cs(), baseContainer); default -> false; }; ck(!isId); }
      var delta= l.bs(); for (var c : l.cs()){ checkC(delta, c); ck(!hasInstance(decs.apply(c.name()))); } var sources= new ArrayList<Sig>();
      for (var parent : l.cs()){ var parentDef= decs.apply(parent.name()); for (var m : parentDef.ms()){
          if (!m.sig().origin().equals(parentDef.name())){ continue; } var s= m.sig(); var canonical= findCanonical(l, s.m(), s.rc()).bs();
          var mapXs= B.xs(push(s.bs(), parentDef.bs())); var mapTs= push(dom(canonical), parent.ts());
          sources.add(new Sig(s.rc(), s.m(), canonical, s.ts().stream().map(ti -> renameT(ti, mapXs, mapTs)).toList(), renameT(s.ret(), mapXs, mapTs), s.origin(), s.abs()));
        } } for (var m : l.ms()){ if (m.sig().origin().equals(l.name())){ sources.add(m.sig()); } }
      sources.stream().collect(Collectors.groupingBy(s -> new Key(s.m(), s.rc()), LinkedHashMap::new, Collectors.toList()))
        .forEach((k,group) -> { var chosen= findCanonical(l, k.m(), k.rc()); group.forEach(s -> sigSub(l, chosen, s)); });
      var g1= g.add(l.thisName(), new IT.RCC(of(l.rc().isoToMut()), new IT.C(l.name(), dom(delta)))); for (var m : l.ms()){ var g2= vpaOf(g1, l, m);
        var allBs= push(delta, m.sig().bs()); m.sig().ts().forEach(t -> kind(allBs, t)); kind(allBs, m.sig().ret()); if (m.e().isEmpty()){ continue; }
        for (int i= 0; i < m.xs().size(); i++){ g2 = g2.add(m.xs().get(i), m.sig().ts().get(i)); } check(allBs, g2, m.e().get(), m.sig().ret());
        for (int i= 0; i < m.xs().size(); i++){ if (!kindOf(allBs, m.sig().ts().get(i), EnumSet.of(mut, read, mutH, readH, imm))){ usedOnce(m, m.xs().get(i)); } }
      } } static void usedOnce(M m, String x){ var active= new ArrayList<E.X>(); collectX(x, m.e().get(), true, active); if (active.isEmpty()){ return; }
      var total= new ArrayList<E.X>(); collectX(x, m.e().get(), false, total); ck(active.size() > 1 || total.size() > 1); }
    static void collectX(String x, E e, boolean activeOnly, ArrayList<E.X> acc){ if (e instanceof E.X v && v.name().equals(x)){ acc.add(v); }
      if (!(activeOnly && e instanceof Literal)){ e.children().forEach(c -> collectX(x, c, activeOnly, acc)); } }
    static Sig findCanonical(Literal l, MName name, RC rc){ return l.ms().stream().map(M::sig).filter(s -> s.m().equals(name) && s.rc() == rc).findFirst().get(); }
    static List<IT> dom(List<B> bs){ return bs.stream().<IT>map(b -> new IT.X(b.x())).toList(); } static boolean isSameShapeSubtype(List<B> bs, IT t1, IT t2){
      if (!eqModXRC(bs, t1.withRC(mut), t2.withRC(mut))){ return false; } var rcs2= intrinsicRCs(bs, t2);
      return intrinsicRCs(bs, t1).stream().allMatch(r1 -> rcs2.stream().allMatch(r1::isSubType)); } void sigSub(Literal l, Sig current, Sig parent){
      var ctx= push(l.bs(), current.bs()); for (int i= 0; i < current.ts().size(); i++){
        ck(!sameOuterRC(ctx, current.ts().get(i), parent.ts().get(i)) || !isSub(ctx, parent.ts().get(i), current.ts().get(i))); }
      ck(!sameOuterRC(ctx, current.ret(), parent.ret()) || !isSub(ctx, current.ret(), parent.ret())); } static boolean sameOuterRC(List<B> bs, IT a, IT b){
      return (a instanceof IT.ReadImmX) == (b instanceof IT.ReadImmX) && a.explicitRC().equals(b.explicitRC()) || eqModXRC(bs, a, b); }
    static boolean eqModXRC(List<B> bs, IT a, IT b){ if (a.equals(b)){ return true; }
      if (!(a instanceof IT.RCC(var aRc, var aC) && b instanceof IT.RCC(var bRc, var bC))){
        if (!(a.withRC(imm) instanceof IT.RCX(_, var x)) || !a.withRC(imm).equals(b.withRC(imm))){ return false; }
        return B.get(bs, x.name()).rcs().size() == 1 && intrinsicRCs(bs, a).equals(intrinsicRCs(bs, b)); }
      return aRc.equals(bRc) && aC.name().equals(bC.name()) && zip(aC.ts(), bC.ts(), (x,y) -> eqModXRC(bs, x, y)).allMatch(v -> v); }
    List<Reason> callTyping(List<B> bs, Gamma g, E.Call c, List<IT> rs){
      if (!(typeOf(bs, g, c.e(), List.of()).getFirst().best() instanceof IT.RCC rcc0)){ throw new Fail(); } var d= decs.apply(rcc0.c().name());
      var sig= d.ms().stream().map(M::sig).filter(s -> s.m().equals(c.name()) && s.rc() == c.rc()).findFirst().orElseThrow(Fail::new);
      ck(sig.bs().size() != c.targs().size()); for (int i= 0; i < c.targs().size(); i++){ kind(bs, c.targs().get(i), sig.bs().get(i).rcs()); }
      var xs= B.xs(push(d.bs(), sig.bs())); var ts0= push(rcc0.c().ts(), c.targs());
      var base= new MType(sig.rc(), sig.ts().stream().map(ti -> renameT(ti, xs, ts0)).toList(), renameT(sig.ret(), xs, ts0)); c.expectedRes().inner = base.t();
      var app= promotions(bs, base).stream().filter(m -> rcc0.rc().get().isSubType(m.rc())).toList(); ck(app.isEmpty());
      var okByArg= new ArrayList<List<Integer>>(); for (int argi= 0; argi < c.es().size(); argi++){ var ai= argi;
        var reqs= app.stream().map(m -> m.ts().get(ai)).distinct().toList(); var resByReq= typeOf(bs, g, c.es().get(argi), reqs);
        ck(resByReq.stream().noneMatch(Reason::isEmpty));
        okByArg.add(IntStream.range(0, app.size()).filter(i -> resByReq.get(reqs.indexOf(app.get(i).ts().get(ai))).isEmpty()).boxed().toList()); }
      var possible= IntStream.range(0, app.size()).boxed().filter(ci -> okByArg.stream().allMatch(ok -> ok.contains(ci))).toList(); ck(possible.isEmpty());
      if (rs.isEmpty()){ return List.of(new Reason(bestUnique(bs, app, possible), true)); } return rs.stream().map(req -> {
        var okRet= possible.stream().filter(i -> isSub(bs, app.get(i).t(), req)).toList();
        return okRet.isEmpty() ? new Reason(bestUnique(bs, app, possible), false) : new Reason(bestUnique(bs, app, okRet), true); }).toList(); }
    IT bestUnique(List<B> bs, List<MType> app, List<Integer> idxs){ var all= idxs.stream().map(i -> app.get(i).t()).toList();
      return all.stream().filter(ti -> all.stream().noneMatch(tj -> !tj.equals(ti) && isSub(bs, tj, ti))).findFirst().get(); } static RC lub(EnumSet<RC> rcs){
      var ubs= Stream.of(RC.values()).filter(u -> rcs.stream().allMatch(x -> x.isSubType(u))).toList();
      return ubs.stream().filter(u -> ubs.stream().allMatch(u::isSubType)).findFirst().get(); } static RC glb(EnumSet<RC> rcs){
      var lbs= Stream.of(RC.values()).filter(l -> rcs.stream().allMatch(l::isSubType)).toList();
      return lbs.stream().filter(l -> lbs.stream().allMatch(x -> x.isSubType(l))).findFirst().get(); } static List<MType> promotions(List<B> d, MType mType){
      var out= new LinkedHashSet<MType>(); out.add(mType); out.add(apply(d, mType, Mode.flexy, Mode.flexy)); out.add(apply(d, mType, Mode.strong, Mode.strong));
      out.add(apply(d, mType, Mode.useRead, Mode.hyg));
      out.add(new MType(Mode.hyg.of(mType.rc()), mType.ts().stream().map(ti -> modeF(d, ti, Mode.flexy, TypeSystem::glb)).toList(), modeF(d, mType.t(), Mode.hyg, TypeSystem::lub)));
      for (int i= 0; i < mType.ts().size(); i++){ var ii= i;
        var tsj= IntStream.range(0, mType.ts().size()).mapToObj(j -> modeF(d, mType.ts().get(j), j == ii ? Mode.hyg : Mode.flexy, TypeSystem::glb)).toList();
        out.add(new MType(Mode.flexy.of(mType.rc()), tsj, modeF(d, mType.t(), Mode.hyg, TypeSystem::lub))); } return List.copyOf(out); }
    static MType apply(List<B> d, MType m, Mode modeP, Mode modeR){
      return new MType(modeP.of(m.rc()), m.ts().stream().map(ti -> modeF(d, ti, modeP, TypeSystem::glb)).toList(), modeF(d, m.t(), modeR, TypeSystem::lub)); }
    static IT modeF(List<B> d, IT t, Mode mode, Function<EnumSet<RC>,RC> f){ return switch (t){ case IT.RCC rcc -> rcc.withRC(mode.of(rcc.rc().get()));
        case IT.RCX rcx -> rcx.withRC(mode.of(rcx.rc())); case IT.X x -> modeVar(d, x, rc -> rc, mode, f, t);
        case IT.ReadImmX(var x) -> modeVar(d, x, RC::readImm, mode, f, t); case IT.U _ -> t; }; }
    static IT modeVar(List<B> d, IT.X x, UnaryOperator<RC> inst, Mode mode, Function<EnumSet<RC>,RC> f, IT original){ var rcs= EnumSet.noneOf(RC.class);
      B.get(d, x.name()).rcs().forEach(rc -> rcs.add(inst.apply(rc))); if (rcs.stream().allMatch(rc -> mode.of(rc) == rc)){ return original; }
      var mapped= EnumSet.noneOf(RC.class); rcs.forEach(rc -> mapped.add(mode.of(rc))); return new IT.RCX(f.apply(mapped), x); } } }
