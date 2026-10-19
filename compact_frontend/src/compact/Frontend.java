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
  static <V> List<V> push(List<V> a, List<V> b){ return Stream.concat(a.stream(), b.stream()).toList(); }
  static <V> List<V> push(List<V> a, V b){ return Stream.concat(a.stream(), Stream.of(b)).toList(); }
  static <V> List<V> push(V a, List<V> b){ return Stream.concat(Stream.of(a), b.stream()).toList(); }
  static <A,B,R> Stream<R> zip(List<A> as, List<B> bs, BiFunction<A,B,R> f){ return IntStream.range(0, as.size()).mapToObj(i -> f.apply(as.get(i), bs.get(i))); }
  @SafeVarargs @SuppressWarnings("varargs") static <V> Stream<V> cat(Stream<V>... ss){ return Stream.of(ss).flatMap(s -> s); }
  static String join(List<?> l, String start, String sep, String end, String empty){
    return l.isEmpty() ? empty : l.stream().map(Object::toString).collect(Collectors.joining(sep, start, end)); }
  public static Object parse(String input){ return new Parser(new Names(List.of(), List.of(), List.of(), null), tokens(input)).parseAll(Parser::parseFileFull); }
  public static List<Literal> compile(String pkgName, Map<String,String> override, Map<String,String> files, List<Literal> otherLits){
    var other= otherLits.stream().collect(Collectors.toMap(Literal::name, d -> d)); var raw= new TreeMap<String,FileFull>();
    files.forEach((path, content) -> raw.put(path, (FileFull)parse(content)));
    var heads= raw.keySet().stream().filter(p -> { var name= p.substring(p.lastIndexOf('/')+1); return name.startsWith("_rank_") && name.contains("."); }).toList();
    ck(heads.size() != 1); var head= raw.get(heads.getFirst());
    ck(raw.values().stream().anyMatch(f -> f != head && !(f.maps().isEmpty() && f.uses().isEmpty())));
    var ds= raw.values().stream().flatMap(f -> f.decs().stream()).toList(); var uses= head.uses().stream().map(FileFull.Use::out).toList();
    var decNames= ds.stream().flatMap(d -> d.owner().decs().stream()).toList(); ck(dup(decNames)); var decStrs= decNames.stream().map(TName::s).toList();
    ck(!Collections.disjoint(decStrs, uses)); ck(ds.stream().flatMap(d -> d.owner().gen().used().stream()).anyMatch(x -> decStrs.contains(x) || uses.contains(x)));
    var map= new HashMap<>(override); for (var u : head.uses()){ var p= map.getOrDefault(u.in().pkgName(), u.in().pkgName());
      var in= p + "." + u.in().simpleName(); map.put(u.out(), in);
      var dom= p.equals(pkgName) ? decNames.stream().map(n -> n.withPkgName(pkgName)) : other.keySet().stream();
      ck(dom.noneMatch(e -> e.s().equals(in))); } var ctx= new Methods(new Pkg(pkgName, map, ds, new HashSet<>(decNames)), other);
    var res= ctx.steps(ctx.registerTypeHeadersAndReturnRoots(toInference(ctx))); TypeSystem.allOk(res, other); return res; } public enum RC{
    imm, mut, read, iso, mutH, readH; boolean isSubType(RC other){ return this == other || other == readH || this == iso || other == read && !isH() || this == mut && other == mutH; }
    boolean isH(){ return this == mutH || this == readH; } boolean isReadOrImm(){ return this == read || this == imm; }
    boolean isIsoOrImm(){ return this == iso || this == imm; } RC isoToMut(){ return this == iso ? mut : this; }
    RC readImm(){ return isIsoOrImm() ? imm : read; } String toStrSpace(){ return this == imm ? "" : this+" "; } } public record TName(String s, int arity){
    static int pkgDot(String s){ return Character.isLowerCase(s.charAt(0)) ? s.indexOf('.') : -1; }
    TName withPkgName(String pkg){ return new TName(pkg+"."+s, arity); }
    TName withArity(int arity){ return new TName(s, arity); }
    String pkgName(){ var i= pkgDot(s); return i == -1 ? "" : s.substring(0, i); }
    String simpleName(){ var i= pkgDot(s); return i == -1 ? s : s.substring(i + 1); } boolean isPublic(){ return !simpleName().startsWith("_"); } }
  public record MName(String s, int arity){ MName withArity(int arity){ return new MName(s, arity); } @Override public String toString(){ return s; } }
  public record B(String x, EnumSet<RC> rcs){ static List<String> xs(List<B> bs){ return bs.stream().map(B::x).toList(); }
    static B get(List<B> bs, String name){ return bs.stream().filter(b -> b.x().equals(name)).findFirst().get(); }
    @Override public String toString(){ return x+":"+join(rcs.stream().toList(), "", ",", "", ""); } }
  enum TK{
    Ws("\\s+"), LineComment("//[^\\n]*"), BlockComment("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"),
    Arrow("->"), ORound("\\("), CRound("\\)"), OCurly("\\{"), CCurlyId("\\}[A-Za-z0-9_]+'*"), CCurly("\\}"),
    OSquareArg("(?<=[A-Za-z0-9_'`\""+TK.op+"])(?<!\\*/)\\["), CSquare("\\]"),
    Underscore("_"), Comma(","), SemiColon(";"), ColonColon("::"), Colon(":"), Eq("="), SQuote("'"), ReadImm("read/imm"), RCap("readH|mutH|imm|iso|read|mut"),
    SignedFloat("[+-]"+TK.flt), UnSignedFloat(TK.flt), SignedInt("[+-]"+TK.nat), UnsignedInt(TK.nat), UStr("\"[^\"\\n]*\""), SStr("`[^`\\n]*`"),
    DotName("\\._*[a-z]"+TK.id), UppercaseId("(?:"+TK.pkg+"\\.)?_*[A-Z]"+TK.id),
    LowercaseId("_*[a-z]"+TK.id), BadSStrQuote("'(?:(?!//|/\\*)[^'\\n\"`])*'(?![_a-z])"), Op("(?:(?!/\\*|\\*/|//)["+TK.op+"])+"),
    _XId("_*[A-Z]"+TK.id), _pkgName(TK.pkg), _use("use"), _map("map"), _as("as"), _in("in"),
    _EOF(""), _SOF(""), _CurlyGroup(""), _SquareGroup(""), _RoundGroup("");
    static final String pkg= "(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*", id= "[A-Za-z0-9_]*'*",
      op= "\\\\/#*\\-+%<>=!&^~?|", nat= "[0-9](?:[0-9_]*[0-9])?", flt= nat+"\\."+nat+"(?:[eE][+-]?"+nat+")?(?:soft)?"; final Pattern p;
    TK(String regex){ p= Pattern.compile(regex); }
    int match(String s, int i){ var m= p.matcher(s).useTransparentBounds(true).region(i, s.length()); return m.lookingAt() ? m.end()-i : -1; } }
  static boolean isKind(String input, TK... kinds){ return Stream.of(kinds).anyMatch(k -> k.match(input, 0) == input.length()); }
  static final TK[] typeName= {UppercaseId, SignedFloat, UnSignedFloat, SignedInt, UnsignedInt, SStr, UStr};
  record Token(TK kind, String content, List<Token> tokens){ boolean is(TK... kinds){ return Stream.of(kinds).anyMatch(k -> k == kind); } }
  static final String allowed= "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>,.;:()[]{}`'\"!?@#$%^&_|~\\ \n";
  static final Map<TK,Map<TK,TK>> groups= Map.of(_SOF, Map.of(_EOF, _EOF), ORound, Map.of(CRound, _RoundGroup), OSquareArg, Map.of(CSquare, _SquareGroup), OCurly, Map.of(CCurly, _CurlyGroup, CCurlyId, _CurlyGroup));
  static List<Token> tokens(String s){ s = s.replaceFirst("^\\uFEFF", "").replaceAll("[\\r\\u2028\\u2029\\u0085]", "\n");
    ck(s.codePoints().anyMatch(c -> allowed.indexOf(c) < 0)); var all= new ArrayList<Token>(); for (int i= 0; i < s.length();){ TK best= null; int len= 0;
      for (var k : TK.values()){ var l= k.match(s, i); if (l > len){ best= k; len= l; } } ck(best == null);
      all.add(new Token(best, s.substring(i, i+len), List.of())); i += len; } var res= new ArrayList<Token>(List.of(new Token(_SOF, "", List.of())));
    for (int i= 0; i < all.size(); i++){ var t= all.get(i); if (t.is(Ws, LineComment, BlockComment)){ continue; }
      var bad= t.is(BadSStrQuote) || t.is(OSquareArg) && all.get(i-1).is(SStr, UStr, SignedInt, UnsignedInt, SignedFloat, UnSignedFloat); ck(bad); res.add(t); }
    res.add(new Token(_EOF, "", List.of())); var it= res.iterator(); return tree(it, it.next()).tokens(); } static Token tree(Iterator<Token> it, Token open){
    var out= new ArrayList<Token>(List.of(open)); while (true){ var c= it.next();
      var g= groups.get(open.kind()).get(c.kind()); if (g != null){ out.add(c); return new Token(g, "", out); }
      if (groups.containsKey(c.kind())){ out.add(tree(it, c)); continue; } ck(groups.values().stream().anyMatch(m -> m.containsKey(c.kind()))); out.add(c); } }
  sealed interface PE{ record X(String name) implements PE{}
    record Lit(Optional<String> thisName, List<PM> methods) implements PE{} record TypedLiteral(RC rc, IT.C c, Optional<Lit> l) implements PE{}
    record DeclarationLiteral(Optional<RC> rc, Declaration dec) implements PE{} record CallSquare(Optional<RC> rc, List<IT> ts){}
    record Call(PE e, MName name, Optional<CallSquare> targs, Optional<XPat> pat, List<PE> es) implements PE{} record Implicit() implements PE{} }
  record PSig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Parameter> parameters, Optional<IT> t){}
  record PM(Optional<PSig> sig, Optional<PE> body, boolean hasImplicit){
    PM(Optional<PSig> sig, Optional<PE> body){ this(sig, body, body.stream().anyMatch(Frontend::hasImplicit)); }
    int arity(){ return sig.map(s -> s.parameters().size()).orElse(0) + (hasImplicit ? 1 : 0); } } static boolean hasImplicit(PE e){ return switch (e){
    case PE.X _, PE.TypedLiteral _, PE.DeclarationLiteral _, PE.Lit _ -> false; case PE.Implicit _ -> true;
    case PE.Call c -> hasImplicit(c.e()) || c.es().stream().anyMatch(Frontend::hasImplicit); };} record Parameter(Optional<XPat> xp, Optional<IT> t){}
  sealed interface XPat{ Stream<String> parameterNames();
    record Name(String x) implements XPat{ @Override public Stream<String> parameterNames(){ return Stream.of(x); } }
    record Destruct(List<List<MName>> extract, String id) implements XPat{
      @Override public Stream<String> parameterNames(){ return extract.stream().map(e -> e.getLast().s().substring(1) + id); } } }
  record Declaration(TName name, List<B> bs, List<IT.C> cs, PE.Lit l, Owner owner){}
  record FileFull(List<String> maps, List<Use> uses, List<Declaration> decs){ record Use(TName in, String out){} }
  record Names(List<String> xs, List<String> Xs, List<String> hiddenXs, Owner owner){ Names add(List<String> xs, List<String> Xs){
      owner.vars().used().addAll(xs); owner.gen().used().addAll(Xs); return new Names(push(this.xs, xs), push(this.Xs, Xs), hiddenXs, owner); } }
  record RCMName(Optional<RC> rc, MName name){} static final class Parser{ Names names; final List<Token> ts; int index= 0; int limit;
    Parser(Names names, List<Token> ts){ this.names= names; this.ts= ts; limit= ts.size(); }
    Parser make(List<Token> tokens){ return new Parser(names, tokens); } <R> R parseAll(Function<Parser,R> r){ var res= r.apply(this); ck(index != limit);
      return res; } boolean end(){ return limit == index; }
    Optional<Token> peek(int la){ var i= index + la; return i >= limit ? empty() : of(ts.get(i)); }
    boolean peek(TK... kinds){ return peekIf(t -> t.is(kinds)); } boolean peekIf(Predicate<Token> p){ return peek(0).map(p::test).orElse(false); }
    @SafeVarargs final boolean peekOrder(Predicate<Token>... ps){ return IntStream.range(0, ps.length).allMatch(i -> peek(i).filter(ps[i]).isPresent()); }
    Token expect(TK... kinds){ var t= peek(0).orElseThrow(Fail::new); ck(kinds.length > 0 && !t.is(kinds)); index += 1; return t; }
    Token expectLast(TK... kinds){ ck(!ts.get(limit - 1).is(kinds)); limit -= 1; return ts.get(limit); }
    boolean fwdIf(boolean v){ if (v){ index += 1; } return v; } <R> R parseGroup(Function<Parser,R> r){
      var res= make(ts.get(index).tokens()).parseAll(r); index += 1; return res; } <R> List<R> splitBy(ToIntFunction<Parser> probe, Function<Parser,R> elem){
      var slice= ts.subList(index, limit); var sp= make(slice); var parts= new ArrayList<Parser>(); while (!sp.end()){ int start= sp.index;
        int drop= probe.applyAsInt(sp); parts.add(make(slice.subList(start, sp.index-drop))); } index = limit; return parts.stream().map(p -> p.parseAll(elem)).toList(); }
    <R> List<R> parseGroupSep(Function<Parser,R> r, TK open, TK close, ToIntFunction<Parser> probe){
      return parseGroup(p -> { p.expect(open); p.expectLast(close); return p.splitBy(probe, r); }); }
    <R> Optional<R> parseFront(ToIntFunction<Parser> probe, Function<Parser,R> first){ var slice= ts.subList(index, limit);
      var sp= make(slice); int drop= probe.applyAsInt(sp); int end= sp.index;
      if (sp.end()){ return empty(); } var res= make(slice.subList(0, end-drop)).parseAll(first); index += end; return of(res); }
    int splitOn(int mode, TK k){ while (!end()){ if (!expect().is(k)){ continue; } if (mode == 2){ index -= 1; } return mode & 1; } return 0; }
    PE parseE(){ var e= parseAtom(); while (!end()){ e = parsePost(e); } return e; }
    boolean isDec(){ return peekOrder(t -> t.is(typeName), t -> t.is(_SquareGroup), t -> t.is(Colon)) || peekOrder(t -> t.is(typeName), t -> t.is(Colon)); }
    PE parseAtom(){ if (peek(LowercaseId)){ var x= expect().content(); ck(!names.xs().contains(x)); return new PE.X(x); }
      if (peek(_RoundGroup)){ return parseGroup(p -> { p.expect(ORound); p.expectLast(CRound); return p.parseE(); }); }
      if (peek(ColonColon)){ expect(); return new PE.Implicit(); } if (peek(_CurlyGroup)){ return parseGroup(p -> p.parseLiteral(false)); }
      var rc= parseOptRC(); ck(rc.stream().anyMatch(RC::isH)); if (isDec()){ return new PE.DeclarationLiteral(rc, parseDeclaration(false)); }
      return new PE.TypedLiteral(rc.orElse(RC.imm), parseC(), parseIf(peek(_CurlyGroup), () -> parseGroup(p -> p.parseLiteral(false)))); }
    RC parseRC(){ return RC.valueOf(expect(RCap).content()); } Optional<RC> parseOptRC(){ return parseIf(peek(RCap), this::parseRC); } IT.C parseC(){
      var c= parseTName(); if (!peek(_SquareGroup)){ return new IT.C(c, List.of()); } var ts= parseGroupSep(Parser::parseT, OSquareArg, CSquare, commaSkip);
      return new IT.C(c.withArity(ts.size()), ts); } TName parseTName(){ var s= expect(typeName).content();
      ck(names.Xs().contains(s) || names.hiddenXs().contains(s)); var res= new TName(s, 0); ck(!res.pkgName().isEmpty() && !res.isPublic()); return res; }
    IT parseT(){ if (fwdIf(peek(ReadImm))){ return new IT.ReadImmX(parseTX(false)); } var rc= parseOptRC();
      if (peekIf(t -> t.is(typeName) && !names.Xs().contains(t.content()))){ return new IT.RCC(of(rc.orElse(RC.imm)), parseC()); }
      var res= parseTX(false); return rc.map(r -> (IT)new IT.RCX(r, res)).orElse(res); } IT.X parseTX(boolean mustNew){
      var c= expectValidate(UppercaseId, _XId).content(); ck(mustNew ? names.Xs().contains(c) || names.hiddenXs().contains(c) : !names.Xs().contains(c));
      return new IT.X(c); } PE parsePost(PE receiver){ if (peek(SignedFloat, SignedInt)){ var num= expect().content();
        var lit= new PE.TypedLiteral(RC.imm, new IT.C(new TName(num.substring(1), 0), List.of()), empty());
        return new PE.Call(receiver, new MName(num.substring(0, 1), 1), empty(), empty(), List.of(lit)); }
      var m= new MName(expect(DotName, Op).content(), 0); var sq= parseIf(peek(_SquareGroup), () -> parseGroup(Parser::parseCallSquare));
      if (peek(_RoundGroup)){ var es= parseGroupSep(Parser::parseE, ORound, CRound, Parser::onCommaExp);
        return new PE.Call(receiver, m.withArity(es.size()), sq, empty(), es); }
      var xpat= parseIf(peekOrder(t -> t.is(LowercaseId, _CurlyGroup), t -> t.is(Eq)), () -> { var r= parseXPat(); index += 1; return r; });
      if (end() || peek(DotName, Op, Colon)){ ck(xpat.isPresent()); return new PE.Call(receiver, m, sq, empty(), List.of()); }
      var atom= parseAtom(); var xs= xsOf(xpat).toList(); checkNewXs(xs);
      ck(xpat.isPresent() && xpat.get() instanceof XPat.Destruct && xs.size() > 31); names = names.add(xs, List.of());
      if (xpat.isEmpty()){ return new PE.Call(receiver, m.withArity(1), sq, xpat, List.of(atom)); } var chain= parsePost(new PE.X(""));
      while (!end()){ chain = parsePost(chain); } return new PE.Call(receiver, m.withArity(2), sq, xpat, List.of(atom, chain)); } XPat parseXPat(){
      if (peek(LowercaseId, Underscore)){ return new XPat.Name(parseDecX().name()); } return parseGroup(Parser::parseDestruct); } XPat.Destruct parseDestruct(){ expect(OCurly);
      var id= expectLast(CCurly, CCurlyId).content().substring(1);
      var chains= splitBy(commaSkip, p -> p.splitBy(q -> { q.expect(); return 0; }, q -> new MName(q.expect(DotName).content(), 0)));
      ck(chains.isEmpty() || chains.stream().anyMatch(List::isEmpty)); var res= new XPat.Destruct(chains, id);
      ck(res.parameterNames().anyMatch(x -> !isKind(x, LowercaseId) || isKind(x, RCap))); return res; } PE.CallSquare parseCallSquare(){ expect(OSquareArg);
      var hasRC= peekOrder(t -> t.is(RCap), t -> t.is(Comma, CSquare)); expectLast(CSquare); var rc= parseIf(hasRC, this::parseRC);
      if (hasRC && !end()){ expect(Comma); } return new PE.CallSquare(rc, splitBy(commaSkip, Parser::parseT)); } PE.X parseDecX(){
      var x= expect(LowercaseId, Underscore).content(); ck(names.xs().contains(x)); return new PE.X(x); } PE.Lit parseLiteral(boolean top){ expect(OCurly);
      expectLast(CCurly); var thisName= parseIf(fwdIf(peek(SQuote)), () -> parseDecX().name()); var n= thisName.orElse(top ? "this" : "_");
      ck(top && !n.equals("this")); if (!n.equals("_")){ names = names.add(List.of(n), List.of()); }
      var ms= splitBy(p -> p.splitOn(1, SemiColon), p -> p.parseMethod(top));
      var ns= ms.stream().flatMap(m -> m.sig().flatMap(s -> s.m().map(nn -> new RCMName(s.rc(), nn.withArity(m.arity())))).stream()).toList(); ck(dup(ns));
      ck(ns.stream().anyMatch(nn -> nn.rc().isEmpty() && ns.stream().anyMatch(o -> o.name().equals(nn.name()) && o.rc().isPresent())));
      ck(dup(ms.stream().filter(m -> m.sig().flatMap(PSig::m).isEmpty()).map(PM::arity).toList())); return new PE.Lit(thisName, ms); }
    Stream<String> xsOf(Optional<XPat> xp){ return xp.stream().flatMap(XPat::parameterNames).filter(x -> !x.equals("_")); }
    void checkNewXs(List<String> xs){ ck(dup(xs) || xs.stream().anyMatch(names.xs()::contains)); }
    PM parseMethodWithSig(PSig sig){ var xs= sig.parameters().stream().flatMap(p -> xsOf(p.xp())).toList(); checkNewXs(xs);
      names = names.add(xs, bsXs(sig.bs())); var m= new PM(of(sig), of(parseAll(Parser::parseE)));
      var hasPats= sig.parameters().stream().flatMap(p -> p.xp().stream()).anyMatch(XPat.Destruct.class::isInstance);
      ck(hasPats && xs.size() + (m.hasImplicit() ? 1 : 0) > 32); return m; }
    static List<String> bsXs(Optional<List<B>> bs){ return B.xs(bs.orElse(List.of())); } PM parseMethod(boolean top){
      var m= parseFront(p -> p.splitOn(1, Arrow), Parser::parseSig).map(this::parseMethodWithSig); if (m.isPresent()){ return m.get(); }
      var hasSig= peek(DotName, Op) || peekOrder(t -> t.is(RCap), t -> t.is(DotName, Op)); if (!hasSig){ return new PM(empty(), of(parseAll(Parser::parseE))); }
      var sig= parseSig(); ck(!top); return new PM(of(sig), empty()); } PSig parseSig(){
      var rc= parseOptRC(); ck(rc.stream().anyMatch(r -> r.isH() || r == RC.iso));
      var m= parseIf(peek(DotName, Op), () -> new MName(expect(DotName, Op).content(), 0)); var bs= parseIf(peek(_SquareGroup), () -> parseBs(true));
      names = names.add(List.of(), bsXs(bs));
      var ps= peek(_RoundGroup) ? parseGroupSep(Parser::parseParameter, ORound, CRound, commaSkip) : peek(Colon) ? List.<Parameter>of() : splitBy(commaSkip, Parser::parseParameter);
      var t= parseIf(fwdIf(peek(Colon)), this::parseT); ck(!end()); var xs= ps.stream().flatMap(p -> xsOf(p.xp())).toList();
      ck(dup(xs)); return new PSig(rc, m, bs, ps, t); } Parameter parseParameter(){
      var x= parseIf(peek(LowercaseId, Underscore, _CurlyGroup), this::parseXPat);
      var p= new Parameter(x, x.isPresent() ? parseIf(fwdIf(peek(Colon)), this::parseT) : of(parseT())); ck(!end()); return p; }
    List<B> parseBs(boolean mustNew){ var res= parseGroupSep(p -> p.parseB(mustNew), OSquareArg, CSquare, Parser::onCommaB); ck(dup(B.xs(res))); return res; } B parseB(boolean mustNew){
      var x= parseTX(mustNew).name(); if (end()){ return new B(x, EnumSet.of(RC.imm)); } expect(Colon); ck(end()); if (!peek(Op)){
        var rcs= splitBy(commaSkip, Parser::parseRC); ck(dup(rcs)); return new B(x, EnumSet.copyOf(rcs)); }
      return switch (expect(Op).content()){ case "**" -> new B(x, EnumSet.allOf(RC.class)); case "*" -> new B(x, EnumSet.of(RC.imm, RC.mut, RC.read));
        default -> throw new Fail(); }; } Declaration parseDeclaration(boolean top){ var c= parseTName(); index -= 1; expectValidate(UppercaseId, _XId);
      var bs= peek(_SquareGroup) ? parseBs(top) : List.<B>of(); var Xs= B.xs(bs); var outer= names; var owner= top ? new Owner() : names.owner();
      names = new Names(names.xs(), List.of(), push(names.hiddenXs(), names.Xs()), owner).add(List.of(), Xs); c = c.withArity(Xs.size()); owner.decs().add(c); expect(Colon);
      var cs= parseFront(p -> p.splitOn(2, _CurlyGroup), p -> p.splitBy(commaSkip, Parser::parseC)).orElseThrow(Fail::new); ck(dup(cs));
      var l= parseGroup(p -> p.parseLiteral(top)); names = outer; return new Declaration(c, bs, cs, l, owner); } FileFull parseFileFull(){ expect(_SOF);
      expectLast(_EOF); var maps= new ArrayList<String>(); var uses= new ArrayList<FileFull.Use>(); Function<Parser,Object> header= p -> {
        if (!p.peek(LowercaseId)){ return ""; } p.expectLast(SemiColon); return p.splitBy(q -> q.splitOn(1, SemiColon), q -> q.parseHeaderElement(maps, uses));
      }; if (parseFront(Parser::headEnd, header).isEmpty()){ parseAll(header); }
      var ds= splitBy(p -> p.splitOn(0, _CurlyGroup), p -> p.parseDeclaration(true)); return new FileFull(maps, uses, ds); }
    Token expectValidate(TK kind, TK validation){ ck(!peekIf(t -> isKind(t.content(), validation))); return expect(kind); }
    Object parseHeaderElement(ArrayList<String> maps, ArrayList<FileFull.Use> uses){ if (fwdIf(peekIf(t -> isKind(t.content(), _map)))){
        var in= expectValidate(LowercaseId, _pkgName).content(); expectValidate(LowercaseId, _as); expectValidate(LowercaseId, _pkgName);
        expectValidate(LowercaseId, _in); var key= in+" "+expectValidate(LowercaseId, _pkgName).content(); ck(maps.contains(key)); maps.add(key); } else{
        ck(!fwdIf(peekIf(t -> isKind(t.content(), _use)))); var t1= parseTName(); expectValidate(LowercaseId, _as);
        var t2= expectValidate(UppercaseId, _XId).content(); ck(uses.stream().anyMatch(u -> u.in().equals(t1) || u.out().equals(t2)));
        uses.add(new FileFull.Use(t1, t2)); } ck(!end()); return null; }
    <R> Optional<R> parseIf(boolean cond, Supplier<R> s){ return cond ? of(s.get()) : empty(); } int onCommaExp(){ var inColon= false; while (!end()){
        var t= expect(); if (t.is(Comma) && !inColon){ return 1; } if (!t.is(_SquareGroup, Comma, UppercaseId)){ inColon = false; }
        if (t.is(Colon)){ inColon = true; } } return 0; } int onCommaB(){ while (!end()){ if (expect().is(Comma) && !peek(RCap)){ return 1; } } return 0; }
    int headEnd(){ while (!(end() || isDec())){ expect(); } return 0; } static final ToIntFunction<Parser> commaSkip= p -> p.splitOn(1, Comma); }
  record Pkg(String name, Map<String,String> map, List<Declaration> decs, Set<TName> decNames){}
  record Scope(HashSet<String> used, HashMap<String,Integer> seq){ Scope(){ this(new HashSet<>(), new HashMap<>()); } }
  record Owner(Scope gen, Scope vars, ArrayList<TName> decs){ Owner(){ this(new Scope(), new Scope(), new ArrayList<>()); } }
  record FreshPrefix(Scope top, HashSet<String> allGenericNames, HashMap<TName,Owner> owners, String pkgName){
    FreshPrefix(Pkg p){ this(new Scope(), new HashSet<>(), new HashMap<>(), p.name());
      for (var tn : p.decNames()){ top.used().add(tn.simpleName()); } top.used().addAll(p.map().keySet());
      for (var d : p.decs()){ allGenericNames.addAll(d.owner().gen().used()); owners.put(d.name().withPkgName(pkgName), d.owner()); } }
    TName freshTopType(TName hint, int arity){
      var res= new TName(pkgName+"."+freshCandidate(hint.simpleName(), "ABCDEFGHJKMNPQRSTUVWXYZ", top, List.of(allGenericNames)), arity); owners.put(res, owners.get(hint)); return res; }
    boolean isFreshGeneric(TName owner, String x, List<String> scope){ return !owners.get(owner).gen().used().contains(x) && !top.used().contains(x) && !scope.contains(x); }
    String freshGeneric(TName owner, String hint, List<String> siblings){
      var cand= freshCandidate(hint, "ABCDEFGHJKMNPQRSTUVWXYZ", owners.get(owner).gen(), List.of(top.used(), siblings)); allGenericNames.add(cand); return cand; }
    String freshVar(TName owner, String hint){ return freshCandidate(hint, "abcdefghjkmnpqrstuvwxyz", owners.get(owner).vars(), List.of()); }
    static String freshCandidate(String hint, String alphabet, Scope s, List<Collection<String>> extraChecks){
      var base= hint.replaceAll("[^A-Za-z0-9]", ""); if (base.length() > 4){ base = base.substring(0, 4); } for (int n= s.seq().getOrDefault(base, 1);; n += 1){
        var sb= new StringBuilder(); for (int k= n; k > 0; k = (k-1) / alphabet.length()){ sb.append(alphabet.charAt((k-1) % alphabet.length())); }
        var cand= "_"+sb.reverse()+base; if (s.used().contains(cand) || extraChecks.stream().anyMatch(e -> e.contains(cand))){ continue; }
        s.used().add(cand); s.seq().put(base, n+1); return cand; } } }
  static final TName baseStr= new TName("base.Str", 0), baseNat= new TName("base.Nat", 0), baseInt= new TName("base.Int", 0), baseFloat= new TName("base.Float", 0),
    widen= new TName("base.WidenTo", 1), sealed= new TName("base.Sealed", 0), captureFree= new TName("base.CaptureFree", 0), baseId= new TName("base.BaseId", 2),
    baseContainer= new TName("base.BaseContainer", 1), inferUnknown= new TName("base.InferUnknown", 0);
  static final List<TName> inferErrs= List.of(new TName("base.InferErr", 2), new TName("base.InferErr", 3), new TName("base.InferErr", 4));
  static boolean has(List<IT.C> cs, TName magic){ return cs.stream().anyMatch(c -> c.name().equals(magic)); }
  static boolean isPrimitiveLiteral(String name){ return "+-1234567890\"`".contains(name.substring(0, 1)); }
  static Literal from(TName n, Function<TName,Literal> map, Map<TName,Literal> other){ var res= map.apply(n); if (res == null){ res = other.get(n); }
    if (res != null || !n.pkgName().equals("base") || !isPrimitiveLiteral(n.simpleName())){ return res; } var s= n.simpleName();
    var lit= s.startsWith("`") || s.startsWith("\"") ? baseStr : isKind(s, UnsignedInt) ? baseNat : isKind(s, SignedInt) ? baseInt : baseFloat;
    var sup= from(lit, map, other); var ms= sup.ms().stream().map(m -> m.withSig(new ISig(m.sig().rc(), m.sig().m(), m.sig().bs(), m.sig().ts(), m.sig().ret(), of(n), false, m.sig().idx()))).toList();
    return new Literal(of(RC.imm), n, List.of(), push(new IT.C(lit, List.of()), sup.cs()), "this", ms, true); }
  static boolean inRange(String raw, BigInteger min, BigInteger max){ var b= new BigInteger(raw.replace("_", "")); return b.compareTo(min) >= 0 && b.compareTo(max) <= 0; }
  static boolean floatOk(String raw){ var soft= raw.endsWith("soft"); var ns= (soft ? raw.substring(0, raw.length()-4) : raw).replace("_", "");
    var d= Double.parseDouble(ns); if (soft){ return Double.isFinite(d); } if (ns.startsWith("+")){ ns = ns.substring(1); }
    if (!Double.isFinite(d)){ return false; } if (d == 0){ return new BigDecimal(ns.replaceAll("[eE].*", "")).signum() == 0; }
    return new BigDecimal(ns).compareTo(new BigDecimal(d)) == 0; } public sealed interface IT{ default boolean isTV(){ return true; }
    default long badness(){ return 0; } default Optional<RC> explicitRC(){ return empty(); } default int depth(){ return 1; }
    record X(String name) implements IT{ @Override public String toString(){ return name; } } record RCX(RC rc, X x) implements IT{
      @Override public String toString(){ return rc.name()+" "+x.name; } @Override public Optional<RC> explicitRC(){ return of(rc); } }
    record ReadImmX(X x) implements IT{ @Override public String toString(){ return "read/imm "+x.name; } } record C(TName name, List<IT> ts, int depth){
      C(TName name, List<IT> ts){ this(name, ts, 1+ts.stream().mapToInt(IT::depth).max().orElse(1)); } @Override public String toString(){ return name.s()+join(ts, "[", ",", "]", ""); } }
    record RCC(Optional<RC> rc, C c) implements IT{ public RCC{ if (c.depth() > 100){ throw new Fail(); } } RCC withTs(List<IT> ts){ return withRCTs(rc, ts); }
      RCC withRCTs(Optional<RC> rc, List<IT> ts){ var c1= new C(c.name(), ts); return c1.depth() > 100 ? this : new RCC(rc, c1); }
      @Override public long badness(){ return c.ts.stream().mapToLong(IT::badness).sum(); }
      @Override public String toString(){ return rc.map(RC::toStrSpace).orElse("AnyRC ")+c; }
      @Override public boolean isTV(){ return c.ts.stream().allMatch(IT::isTV); } @Override public int depth(){ return c.depth(); }
      @Override public Optional<RC> explicitRC(){ return rc; } } enum U implements IT{ Instance; @Override public String toString(){ return "?";}
      @Override public boolean isTV(){ return false; } @Override public long badness(){ return 1; } } default IT withRC(RC rc){ return switch (this){
      case RCC(_, var c) -> new RCC(of(rc), c); case RCX(_, var x) -> new RCX(rc, x); case X x -> new RCX(rc, x);
      case ReadImmX(var x) -> new RCX(rc, x); case U _ -> this; };} default Stream<String> ftv(){ return switch (this){ case X(var name) -> Stream.of(name);
      case RCX(_, var x) -> x.ftv(); case ReadImmX(var x) -> x.ftv(); case RCC(_, var c) -> c.ts().stream().flatMap(IT::ftv); case U _ -> Stream.of(); };}
    default IT readImm(){ return switch (this){ case X x -> new ReadImmX(x); case ReadImmX _ -> this;
      case RCC(var rc, var c) -> new RCC(rc.map(RC::readImm), c); case RCX(var rc, var x) -> new RCX(rc.readImm(), x); case U _ -> this; };} }
  public sealed interface IE{ IT t(); IE withT(IT t); default Stream<IE> children(){ return switch (this){
      case X _, Type _ -> Stream.of(); case Literal l -> l.ms().stream().flatMap(m -> m.e().stream()); case Call c -> Stream.concat(Stream.of(c.e()), c.es().stream()); };}
    record X(String name, IT t) implements IE{ X(String name){ this(name, IT.U.Instance); }
      @Override public IE withT(IT t){ return t.equals(this.t) ? this : new X(name, t); } @Override public String toString(){ return name; } }
    record Type(IT.RCC type, IT t) implements IE{ Type(IT.RCC type){ this(type, IT.U.Instance); }
      @Override public IE withT(IT t){ return t.equals(this.t) ? this : new Type(type, t); } @Override public String toString(){ return type.toString(); } }
    record Call(IE e, MName name, Optional<RC> rc, List<IT> targs, List<IE> es, IT t, boolean written) implements IE{
      Call(IE e, MName name, Optional<RC> rc, List<IT> targs, List<IE> es, boolean written){ this(e, name, rc, targs, es, IT.U.Instance, written); }
      Call withMore(IE e, RC rc, List<IT> targs, List<IE> es, IT t){
        if (e == this.e && this.rc.equals(of(rc)) && targs.equals(this.targs) && es == this.es && t.equals(this.t)){ return this; }
        return new Call(e, name, of(rc), targs, es, t, written); }
      Call withEEs(IE e, List<IE> es){ return e == this.e && es == this.es ? this : new Call(e, name, rc, targs, es, t, written); }
      @Override public Call withT(IT t){ return t.equals(this.t) ? this : new Call(e, name, rc, targs, es, t, written); }
      @Override public String toString(){ return ""+e+name+"["+rc.get()+join(targs, ",", ",", "", "")+"]"+join(es, "(", ", ", ")", ""); } } }
  public record Literal(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<IM> ms, IT t, boolean infName, boolean infHead) implements IE{
    Literal(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<IM> ms, boolean infName){
      this(rc, name, bs, cs, thisName, ms, IT.U.Instance, infName, false); }
    @Override public Literal withT(IT t){ return t.equals(this.t) ? this : new Literal(rc, name, bs, cs, thisName, ms, t, infName, infHead); }
    Literal withMsT(List<IM> ms, IT t){ if (infHead && ms == this.ms && t.equals(this.t)){ return this; }
      return new Literal(rc, name, bs, cs, thisName, ms, t, infName, true); } Literal withCsMs(List<IT.C> cs, List<IM> ms, boolean setInfHead){
      if (infHead == setInfHead && cs.equals(this.cs) && ms == this.ms){ return this; }
      return new Literal(rc, name, bs, cs, thisName, ms, t, infName, setInfHead); }
    Literal withRC(RC rc){ return new Literal(of(rc), name, bs, cs, thisName, ms, infName); }
    @Override public String toString(){ return rc.get()+" "+name.s()+join(bs, "[", ",", "]", "")+":"+join(cs, "", ", ", "", "")+"{'"+thisName+" "+join(ms, "", "; ", "", "")+"}"; } }
  public record IM(ISig sig, List<String> xs, Optional<IE> e){ IM(ISig sig){ this(sig, Collections.nCopies(sig.ts().size(), "_"), empty()); }
    IM withSig(ISig sig){ return sig.equals(this.sig) ? this : new IM(sig, xs, e); }
    @Override public String toString(){ return sig.rc().get().toStrSpace()+sig.m().get()+join(sig.bs().get(), "[", ",", "]", "")+join(zip(xs, sig.ts(), (x,t) -> x+":"+t).toList(), "(", ", ", ")", "")
      +":"+sig.ret()+e.map(body -> "->"+body).orElse(""); } }
  public record ISig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<IT> ts, IT ret, Optional<TName> origin, boolean abs, int idx){
    ISig(RC rc, MName m, List<B> bs, List<IT> ts, IT ret, TName origin, boolean abs, int idx){
      this(of(rc), of(m), of(bs), ts, ret, of(origin), abs, idx); }
    ISig withTsT(List<IT> ts, IT ret){ return new ISig(rc, m, bs, ts, ret, origin, abs, idx); }
    ISig withOrigin(TName origin){ return new ISig(rc, m, bs, ts, ret, of(origin), abs, idx); } }
  static final class IGamma{
    record Frame(RC rc, List<B> bs, HashMap<String,IT> vars){}
    final ArrayList<Frame> fs= new ArrayList<>(List.of(new Frame(null, List.of(), new HashMap<>())));
    int at(String x){ return IntStream.range(0, fs.size()).filter(i -> fs.get(i).vars().containsKey(x)).findFirst().orElse(-1); }
    IT get(String x){ var i= at(x); return i == -1 ? null : fs.get(i).vars().get(x); } IT getWithRC(String x){ var i= at(x); var t= get(x);
      for (var s= i + 1; s < fs.size(); s += 1){ t = adapt(t, fs.get(s).rc(), fs.get(s).bs()); } return t; } boolean notFunnelledInto(String x){
      var fxs= get(x).ftv().toList(); return IntStream.range(at(x) + 1, fs.size()).anyMatch(s -> !B.xs(fs.get(s).bs()).containsAll(fxs)); }
    static IT adapt(IT t, RC rc, List<B> bs){ var x= t instanceof IT.X(var n) ? n : t instanceof IT.ReadImmX(IT.X(var n)) ? n : null; if (x != null){
        var xRcs= B.get(bs, x).rcs(); if (rc == RC.imm || EnumSet.of(RC.iso, RC.imm).containsAll(xRcs)){ return t.withRC(RC.imm); }
        if (xRcs.stream().anyMatch(RC::isH)){ return t; } return rc == RC.read || xRcs.contains(RC.iso) ? t.readImm() : t; } var trc= t.explicitRC();
      if (rc == RC.imm || trc.equals(of(RC.iso))){ return t.withRC(RC.imm); } if (rc == RC.mut){ return t; }
      if (trc.equals(of(RC.mutH))){ return t.withRC(RC.readH); } return trc.equals(of(RC.mut)) ? t.withRC(RC.read) : t; }
    void declare(String x, IT t){ if (!x.equals("_")){ fs.getLast().vars().put(x, t); } }
    Object snap(){ var m= new HashMap<String,IT>(); fs.forEach(f -> m.putAll(f.vars())); return m; } }
  static IT.C normC(IT.C c){ return new IT.C(c.name(), c.ts().stream().map(Frontend::norm).toList()); } static IT norm(IT t){ return switch (t){
    case IT.RCC(var rc, var c) -> new IT.RCC(of(rc.orElse(RC.imm)), normC(c)); case IT.U _ -> inferUnknownT; default -> t; };}
  static final IT.RCC inferUnknownT= new IT.RCC(of(RC.imm), new IT.C(inferUnknown, List.of()));  static boolean isInfer(IT t){ return t instanceof IT.RCC(_, var c) && (c.name().equals(inferUnknown) || inferErrs.contains(c.name())); }
  static IT rename(IT t, List<String> xs, List<IT> ts){ return switch (t){ case IT.X x -> xs.contains(x.name()) ? ts.get(xs.indexOf(x.name())) : x;
      case IT.RCX(var rc, var x) -> { var r= rename(x, xs, ts); yield isInfer(r) ? r : r.withRC(rc); } case IT.RCC rcc -> rcc.withTs(renameIT(rcc.c().ts(), xs, ts));
      case IT.ReadImmX(var x) -> { var r= rename(x, xs, ts); yield isInfer(r) ? r : r.readImm(); } case IT.U _ -> t; }; }
  static List<IT> renameIT(List<IT> tsi, List<String> xs, List<IT> ts){ return tsi.stream().map(ti -> rename(ti, xs, ts)).toList(); }
  static List<IT> toXs(List<String> xs){ return xs.stream().<IT>map(IT.X::new).toList(); }
  static List<IT> qMarks(int n){ return Stream.<IT>generate(() -> IT.U.Instance).limit(n).toList(); }
  record MSigL(RC rc, List<String> xs, List<B> clsBs, List<IT> clsArgs, List<B> methBs, List<IT> ps0, IT ret0){
    MSigL withClsArgs(List<IT> clsArgs){ return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0); }
    IT inst(IT t, List<IT> targs){ return rename(t, xs, push(clsArgs, fixTargs(targs, methBs.size()))); }
    static List<IT> fixTargs(List<IT> targs, int n){ return targs.size() > n ? targs.subList(0, n) : push(targs, qMarks(n-targs.size())); } }
  static Stream<String> ftvE(IGamma g, IE e){ return switch (e){
    case IE.X(var name, var t) -> Stream.concat(t.ftv(), Stream.ofNullable(g.get(name)).flatMap(IT::ftv));
    case Literal l -> cat(l.bs().stream().map(B::x), ftvCs(l.cs()), ftvMs(g, l.ms()));
    case IE.Call(var ei, _, _, var targs, var es, _, _) -> cat(ftvE(g, ei), targs.stream().flatMap(IT::ftv), es.stream().flatMap(x -> ftvE(g, x)));
    case IE.Type(var t, _) -> t.ftv(); };}
  static Stream<String> ftvCs(List<IT.C> cs){ return cs.stream().flatMap(c -> c.ts().stream().flatMap(IT::ftv)); }
  static Stream<String> ftvMs(IGamma g, List<IM> ms){ return ms.stream().flatMap(m -> { var domBs= B.xs(m.sig().bs().orElse(List.of()));
      return cat(m.sig().ts().stream().flatMap(IT::ftv), m.sig().ret().ftv(), m.e().stream().flatMap(ei -> ftvE(g, ei))).filter(x -> !domBs.contains(x));
    }); } static IE dup(FreshPrefix fresh, IE e){ return switch (e){ case IE.X(var name, var t) -> new IE.X(name, t);
    case IE.Type(var type, var t) -> new IE.Type(type, t);
    case IE.Call c -> new IE.Call(dup(fresh, c.e()), c.name(), c.rc(), c.targs(), c.es().stream().map(x -> dup(fresh, x)).toList(), c.t(), c.written());
    case Literal l -> { ck(!l.infName()); var newName= fresh.freshTopType(l.name(), l.name().arity());
      yield new Literal(l.rc(), newName, l.bs(), l.cs(), l.thisName(), l.ms().stream().map(m -> dupM(fresh, m, l.name(), newName)).toList(), l.t(), true, l.infHead());
    } };} static IM dupM(FreshPrefix fresh, IM m, TName oldName, TName newName){
    var sig= m.sig().origin().equals(of(oldName)) ? m.sig().withOrigin(newName) : m.sig();
    return new IM(sig, m.xs(), m.e().map(ei -> dup(fresh, ei))); } static List<Literal> toInference(Methods meths){ var v= new Visitor(meths);
    for (var di : meths.p.decs()){ v.currentTop = v.f(di.name()); v.addDeclaration(v.currentTop, RC.mut, di, true); } return v.decs; } record XE(String x, PE e){}
  static final class Visitor{ final Methods meths; TName currentTop; final ArrayList<String> implicits= new ArrayList<>(); final ArrayList<Literal> decs= new ArrayList<>();
    Visitor(Methods meths){ this.meths= meths; } TName f(TName tn){ var p= meths.p; var pN= tn.pkgName(); if (pN.isEmpty() && isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
      var mapped= pN.isEmpty() ? p.map().get(tn.s()) : null;
      var full= pN.isEmpty() ? (mapped == null ? tn.withPkgName(p.name()) : new TName(mapped, tn.arity())) : new TName(p.map().getOrDefault(pN, pN)+"."+tn.simpleName(), tn.arity());
      ck(!(full.pkgName().equals(p.name()) ? p.decNames().contains(new TName(full.simpleName(), full.arity())) : meths.other.containsKey(full))); return full; }
    IT visitT(IT t){ return t instanceof IT.RCC(var rc, var c) ? new IT.RCC(rc, visitC(c)) : t; } IE visitE(PE e){ return switch (e){
        case PE.X x -> new IE.X(x.name()); case PE.Implicit n -> new IE.X(implicits.getLast());
        case PE.TypedLiteral t -> t.l().isEmpty() ? new IE.Type(new IT.RCC(of(t.rc()), visitC(t.c()))) : liftLiteral(of(t.rc()), List.of(visitC(t.c())), t.l().get());
        case PE.DeclarationLiteral c -> { var name= f(c.dec().name()); meths.fresh.owners().put(name, meths.fresh.owners().get(currentTop));
          yield addDeclaration(name, c.rc().orElse(RC.imm), c.dec(), false); } case PE.Lit l -> liftLiteral(empty(), List.of(), l); case PE.Call c0 -> {
          var c= c0.pat().isPresent() ? desugarCPat(c0) : c0; var recv= visitE(c.e()); var es= c.es().stream().map(this::visitE).toList();
          var sq= c.targs().orElse(new PE.CallSquare(empty(), List.of()));
          yield new IE.Call(recv, c.name(), sq.rc(), sq.ts().stream().map(this::visitT).toList(), es, c.targs().isPresent()); } }; } IT.C visitC(IT.C c){ var s= c.name().s();
      var bad= isPrimitiveLiteral(s) && (isKind(s, UnsignedInt) && !inRange(s, BigInteger.ZERO, new BigInteger(Long.toUnsignedString(-1L)))
        || isKind(s, SignedInt) && !inRange(s, BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE))
        || isKind(s, SignedFloat, UnSignedFloat) && !floatOk(s)); ck(bad); return new IT.C(f(c.name()), c.ts().stream().map(this::visitT).toList()); }
    String parameterToName(Parameter p, boolean hasPat){ if (p.xp().isEmpty()){ return "_"; } return switch (p.xp().get()){
        case XPat.Name(var x) -> hasPat && !x.equals("_") ? meths.fresh.freshVar(currentTop, x) : x;
        case XPat.Destruct _ -> meths.fresh.freshVar(currentTop, "div"); }; }
    List<IM> visitMs(List<PM> ms){ return IntStream.range(0, ms.size()).mapToObj(i -> visitM(ms.get(i), i)).toList(); }
    ISig visitMSig(PM mm, int idx){ IT u= IT.U.Instance;
      if (mm.sig().isEmpty()){ return new ISig(empty(), empty(), empty(), mm.hasImplicit() ? List.of(u) : List.of(), u, empty(), false, idx); }
      var s= mm.sig().get(); var ts= s.parameters().stream().map(p -> p.t().map(this::visitT).orElse(u)).toList(); if (mm.hasImplicit()){ ts = push(ts, u); }
      return new ISig(s.rc(), s.m().map(mi -> mi.withArity(mm.arity())), s.bs(), ts, s.t().map(this::visitT).orElse(u), empty(), mm.body().isEmpty(), idx); } IM visitM(PM m, int idx){ var sig= visitMSig(m, idx);
      if (m.body().isEmpty()){ return new IM(sig); } var body= m.body().get(); var original= m.sig().map(s -> s.parameters()).orElse(List.of());
      var hasPat= original.stream().anyMatch(p -> p.xp().stream().anyMatch(XPat.Destruct.class::isInstance));
      var ps= original.stream().map(p -> parameterToName(p, hasPat)).toList();
      var xpats= zip(ps, original, (x,p) -> p.xp().stream().flatMap(xp -> xpat(xp, x))).flatMap(s -> s).toList(); if (m.hasImplicit()){
        var p= meths.fresh.freshVar(currentTop, "impl"); var inner= hasPat ? meths.fresh.freshVar(currentTop, "impl") : p; ps = push(ps, p);
        if (hasPat){ xpats = push(xpats, new XE(inner, new PE.X(p))); } implicits.add(inner); } if (hasPat){
        var pps= xpats.stream().map(xe -> new Parameter(of(new XPat.Name(xe.x)), empty())).toList();
        var fl= new PE.Lit(empty(), List.of(new PM(of(new PSig(empty(), empty(), empty(), pps, empty())), of(body), false)));
        body = new PE.Call(new PE.TypedLiteral(RC.imm, new IT.C(new TName("base.Destruct", 0), List.of()), empty()), new MName("#", xpats.size()+1), empty(), empty(), push(xpats.stream().map(XE::e).toList(), fl));
      } var e= visitE(body); if (m.hasImplicit()){ implicits.removeLast(); } return new IM(sig, ps, of(e)); }
    Stream<XE> xpat(XPat xp, String lowered){ return switch (xp){ case XPat.Destruct d -> zip(d.extract(), d.parameterNames().toList(), (e,x) -> {
        PE res= new PE.X(lowered); for (var m : e){ res = new PE.Call(res, new MName(m.s(), 0), empty(), empty(), List.of()); } return new XE(x, res); });
      case XPat.Name(var x) -> x.equals(lowered) ? Stream.of() : Stream.of(new XE(x, new PE.X(lowered))); };}
    Literal liftLiteral(Optional<RC> rc, List<IT.C> impl, PE.Lit l){ var ms= visitMs(l.methods());
      return new Literal(rc, meths.fresh.freshTopType(currentTop, 0), List.of(), impl, l.thisName().orElse("_"), ms, true); }
    Literal addDeclaration(TName name, RC rc, Declaration d, boolean top){ var thisName= d.l().thisName().orElse(top ? "this" : "_");
      var bs= d.bs(); var cs= d.cs().stream().map(this::visitC).toList();
      ck(duplicatedSupertypes(bs, cs.stream().map(Frontend::normC).toList()));
      var l= new Literal(of(rc), name, bs, cs, thisName, visitMs(d.l().methods()), false); decs.add(l); return l;
    } PE.Call desugarCPat(PE.Call c){ var fresh= new PE.X(meths.fresh.freshVar(currentTop, "eqS")); var res= replaceAtom(c.es().get(1), fresh);
      var sig= new PSig(empty(), empty(), empty(), List.of(new Parameter(c.pat(), empty()), new Parameter(of(new XPat.Name(fresh.name())), empty())), empty());
      var par2= new PE.Lit(empty(), List.of(new PM(of(sig), of(res), false)));
      return new PE.Call(c.e(), c.name(), c.targs(), empty(), List.of(c.es().getFirst(), par2)); } PE replaceAtom(PE par, PE atom){
      if (!(par instanceof PE.Call c)){ return atom; } return new PE.Call(replaceAtom(c.e(), atom), c.name(), c.targs(), c.pat(), c.es()); } }
  static boolean duplicatedSupertypes(List<B> bs, List<IT.C> cs){ var ts= cs.stream().map(c -> new IT.RCC(of(RC.imm), c)).toList();
    return IntStream.range(0, ts.size()).anyMatch(j -> IntStream.range(0, j).anyMatch(i -> TypeSystem.isSameShapeSubtype(bs, ts.get(i), ts.get(j)) && TypeSystem.isSameShapeSubtype(bs, ts.get(j), ts.get(i))));
  } static final class Methods{
    final Pkg p; final Map<TName,Literal> other; final FreshPrefix fresh; final HashMap<TName,Literal> cache= new HashMap<>();
    final IdentityHashMap<IE,Object> memo= new IdentityHashMap<>();
    Methods(Pkg p, Map<TName,Literal> other){ this.p= p; this.other= other; fresh= new FreshPrefix(p); }
    List<Literal> registerTypeHeadersAndReturnRoots(List<Literal> iDecs){ var rem= new LinkedHashMap<TName,Literal>();
      iDecs.forEach(d -> rem.put(d.name(), d)); var acc= new ArrayList<Literal>(); while (!rem.isEmpty()){
        var layer= rem.values().stream().filter(d -> d.cs().stream().noneMatch(c -> c.name().pkgName().equals(p.name()) && rem.containsKey(c.name()))).toList();
        ck(layer.isEmpty()); for (var d : layer){ rem.remove(d.name()); var e= expandDeclaration(d, false); if (d.thisName().equals("this")){ acc.add(e); }
          register(e); } } return acc; } List<IT.C> fetchCs(IT.C c){ var d= from(c.name()); if (d == null){ return List.of(); }
      return d.cs().stream().map(ci -> new IT.C(ci.name(), renameIT(ci.ts(), B.xs(d.bs()), c.ts()))).distinct().toList(); }
    List<ISig> fetchSigs(Literal child, IT.C c, Literal d, List<String> scope){ return d.ms().stream().map(m -> alphaSig(m, d, c, child, scope)).toList(); }
    ISig alphaSig(IM m, Literal d, IT.C c, Literal child, List<String> scope){ var s= m.sig(); var fullXs= new ArrayList<>(B.xs(d.bs()));
      var fullTs= new ArrayList<>(c.ts()); var newBs= new ArrayList<B>(); for (var b : s.bs().get()){ var x= b.x();
        if (fresh.isFreshGeneric(child.name(), x, scope)){ newBs.add(b); continue; } fullXs.add(x);
        var newX= new IT.X(fresh.freshGeneric(child.name(), x, push(B.xs(s.bs().get()), scope))); fullTs.add(newX); newBs.add(new B(newX.name(), b.rcs())); }
      return new ISig(s.rc(), s.m(), of(newBs), renameIT(s.ts(), fullXs, fullTs), rename(s.ret(), fullXs, fullTs), s.origin(), s.abs(), s.idx()); }
    Literal from(TName name){ return Frontend.from(name, cache::get, other); } Literal expandDeclaration(Literal d, boolean setInfHead){
      var ds= d.cs().stream().map(c -> fetchSigs(d, c, from(c.name()), List.of())).toList();
      var implied= d.cs().stream().flatMap(c -> fetchCs(c).stream()).toList();
      var allCs= ToCore.distinctTypes(d.bs(), push(d.cs(), implied.stream().sorted(Comparator.comparing(Object::toString)).toList()));
      var allSig= zip(d.cs(), ds, (c,sigs) -> implied.contains(c) ? Stream.<ISig>of() : sigs.stream()).flatMap(s -> s).toList();
      var res= d.withCsMs(allCs, pairWithSig(inferMNames(d.ms(), new ArrayList<>(allSig)), new ArrayList<>(allSig), d), setInfHead);
      checkMagicSupertypes(res, allCs); return res; } Literal expandLiteral(Literal d, IT.C c, List<B> scope){ var dd= from(c.name());
      List<ISig> allSig= dd == null ? List.of() : fetchSigs(d, c, dd, B.xs(scope));
      return d.withCsMs(push(c, fetchCs(c)), pairWithSig(inferMNames(d.ms(), new ArrayList<>(allSig)), new ArrayList<>(allSig), d), true); }
    void checkMagicSupertypes(Literal d, List<IT.C> allCs){ ck(allCs.stream().filter(c -> c.name().equals(widen)).count() > 1);
      if (allCs.stream().anyMatch(c -> c.name().equals(baseId))){ var ms= d.ms();
        ck(ms.size() != 1 || !ms.getFirst().sig().m().get().equals(new MName("#", 1))); var s= ms.getFirst().sig();
        ck(!(ms.getFirst().e().isPresent() || s.abs() || has(from(s.origin().get()).cs(), baseId))); }
      if (allCs.stream().noneMatch(c -> c.name().equals(sealed))){ return; }
      ck(allCs.stream().anyMatch(c -> !c.name().pkgName().equals(d.name().pkgName()) && has(from(c.name()).cs(), sealed))); } void register(Literal d){
      var ms= d.ms().stream().map(m -> m.withSig(ToCore.sig(m.sig(), m.sig()))).toList();
      cache.put(d.name(), new Literal(of(d.rc().orElse(RC.imm)), d.name(), d.bs(), d.cs().stream().map(Frontend::normC).toList(), d.thisName(), ms, d.infName())); }
    List<IM> inferMNames(List<IM> ms, ArrayList<ISig> ss){ ss.removeIf(s -> ms.stream().anyMatch(m -> m.sig().m().equals(s.m())));
      var named= ms.stream().filter(m -> m.sig().m().isPresent()).toList(); if (named.size() == ms.size()){ return ms; }
      return push(named, ms.stream().filter(m -> m.sig().m().isEmpty()).map(m -> nameFromSigs(m, ss)).toList()); } IM nameFromSigs(IM m, ArrayList<ISig> ss){
      var arity= m.sig().ts().size(); for (var abs : List.of(true, false)){
        var match= ss.stream().filter(s -> s.m().get().arity() == arity && (s.abs() || !abs)).toList(); ss.removeAll(match);
        var count= match.stream().map(s -> s.m().get()).distinct().count(); ck(count > 1); if (count == 1){ var s= m.sig();
          return new IM(new ISig(s.rc(), match.getFirst().m(), s.bs(), s.ts(), s.ret(), s.origin(), s.abs(), s.idx()), m.xs(), m.e()); } } throw new Fail(); }
    List<IM> pairWithSig(List<IM> ms, ArrayList<ISig> ss, Literal origin){ var res= new ArrayList<IM>(); for (var m : ms){
        var name= m.sig().m().get(); var rc= m.sig().rc();
        var taken= ss.stream().filter(s -> s.m().get().equals(name) && (rc.isEmpty() || rc.equals(s.rc()))).toList(); ss.removeAll(taken);
        var match= taken.stream().collect(Collectors.groupingBy(s -> s.rc().get(), LinkedHashMap::new, Collectors.toList()));
        if (rc.isEmpty() && match.size() > 1 && noH(origin.rc().or(origin.t()::explicitRC).orElse(RC.imm)).isReadOrImm()){
          var dead= match.remove(RC.mut); if (dead != null){ ss.addAll(dead); } } var first= true;
        for (var matches : match.isEmpty() ? List.of(List.<ISig>of()) : match.values()){
          var mi= first ? m : dupM(fresh, m, origin.name(), origin.name()); first = false; res.add(pairWithSig(matches, of(mi), origin)); } }
      ss.stream().collect(Collectors.groupingBy(s -> new RCMName(s.rc(), s.m().get()), LinkedHashMap::new, Collectors.toList())).values().forEach(v -> res.add(pairWithSig(v, empty(), origin)));
      return res.size() == ms.size() ? norm(ms, res) : res; }
    IM pairWithSig(List<ISig> ss, Optional<IM> om, Literal origin){ if (om.isEmpty() && ss.size() == 1){ return new IM(ss.getFirst()); }
      var s= om.map(IM::sig).orElseGet(() -> new ISig(empty(), empty(), empty(), qMarks(ss.getFirst().m().get().arity()), IT.U.Instance, empty(), false, 0));
      if (ss.isEmpty()){ ck(s.ts().stream().anyMatch(t -> t instanceof IT.U) || s.ret() instanceof IT.U);
        return om.get().withSig(new ISig(s.rc().orElse(RC.imm), s.m().get(), s.bs().orElse(List.of()), s.ts(), s.ret(), origin.name(), om.get().e().isEmpty(), s.idx())); }
      var bs= s.bs().orElse(ss.getFirst().bs().get()); var rcss= ss.stream().map(e -> e.bs().get().stream().map(B::rcs).toList()).distinct().toList();
      ck(rcss.size() != 1 || !rcss.getFirst().equals(bs.stream().map(B::rcs).toList()));
      var ssAligned= alignMethodSigsTo(ss, bs); var first= ssAligned.getFirst();
      var ts= IntStream.range(0, s.ts().size()).mapToObj(i -> s.ts().get(i) instanceof IT.U ? agreement(origin, ssAligned, e -> e.ts().get(i)) : s.ts().get(i)).toList();
      var res= s.ret() instanceof IT.U ? agreement(origin, ssAligned, ISig::ret) : s.ret();
      var impl= om.isPresent() ? List.<TName>of() : ssAligned.stream().filter(e -> !e.abs() && !overridden(e, origin)).map(e -> e.origin().get()).distinct().toList(); ck(impl.size() > 1);
      var sig= new ISig(s.rc().orElse(first.rc().get()), first.m().get(), bs, ts, res, impl.size() == 1 ? impl.getFirst() : origin.name(), om.map(mi -> mi.e().isEmpty()).orElse(impl.isEmpty()), s.idx());
      return om.map(mi -> mi.withSig(sig)).orElseGet(() -> new IM(sig)); } boolean overridden(ISig s, Literal lit){ var sup= s.origin().get(); return lit.cs().stream()
        .flatMap(c -> Stream.concat(Stream.of(c.name()), from(c.name()).cs().stream().map(IT.C::name))) .anyMatch(t -> { var d= from(t);
          return !t.equals(sup) && has(d.cs(), sup) && d.ms().stream().map(IM::sig).anyMatch(o -> o.origin().get().equals(d.name()) && o.m().equals(s.m()) && o.rc().equals(s.rc()));
        }); } IT agreement(Literal lit, List<ISig> ss, Function<ISig,IT> f){ var res= ss.stream().map(f).distinct().toList();
      var bs= push(lit.bs(), ss.getFirst().bs().get()); var first= Frontend.norm(res.getFirst());
      ck(!res.stream().allMatch(t -> TypeSystem.eqModXRC(bs, first, Frontend.norm(t)))); return res.getFirst(); }
    List<ISig> alignMethodSigsTo(List<ISig> ss, List<B> targetBs){ return ss.stream().map(superSig -> {
        var fromXs= B.xs(superSig.bs().get()); var toITs= toXs(B.xs(targetBs));
        return new ISig(superSig.rc(), superSig.m(), of(targetBs), renameIT(superSig.ts(), fromXs, toITs), rename(superSig.ret(), fromXs, toITs), superSig.origin(), superSig.abs(), superSig.idx());
      }).toList(); } List<Literal> steps(List<Literal> tops){
      return tops.stream().map(l -> { var di= cache.get(l.name()); var ms= zip(l.ms(), di.ms(), (m,mCore) -> stepDecM(di, mCore, m)).toList();
        return new Literal(di.rc(), di.name(), di.bs(), di.cs(), di.thisName(), ms, di.infName()); }).toList(); }
    IM stepDecM(Literal di, IM mCore, IM m){
      if (m.e().isEmpty()){ return mCore; } var e= m.e().get(); var xs= m.xs(); var ei= meet(e, mCore.sig().ret()); var g= new IGamma();
      for (int i= 0; i < xs.size(); i++){ g.declare(xs.get(i), mCore.sig().ts().get(i)); }
      g.declare(di.thisName(), new IT.RCC(mCore.sig().rc(), new IT.C(di.name(), toXs(B.xs(di.bs()))))); var bs= push(di.bs(), m.sig().bs().get());
      ei = nextStar(bs, g, ei); return new IM(mCore.sig(), xs, of(new ToCore(bs).of(ei, e))); } IE meet(IE e, IT t){
      if (e instanceof IE.Type tt){ return nextT(tt); } if (e instanceof Literal l && l.t().isTV()){ return e; } e = prototypeAscribeRootReceiver(e, t, false);
      return e.withT(meet(e.t(), t)); } IT leastBad(IT.RCC a, IT.RCC b){ var aSuper= isASuperB(a.c().name(), b.c().name());
      var bSuper= isASuperB(b.c().name(), a.c().name());
      var aBad= bSuper ? Math.max(adaptedSuperTs(a, b.c().name()).getFirst().badness(), a.badness()) : a.badness();
      var bBad= aSuper ? Math.max(adaptedSuperTs(b, a.c().name()).getFirst().badness(), b.badness()) : b.badness();
      if (aBad != bBad){ return aBad < bBad ? a : b; } if (aSuper){ return b; } if (bSuper){ return a; }
      if (a.depth() != b.depth()){ return a.depth() < b.depth() ? a : b; } return a.c().name().s().compareTo(b.c().name().s()) < 0 ? a : b; }
    IT leastBad(IT a, IT b){ var ra= rank(a); var rb= rank(b); return ra != rb ? (ra > rb ? a : b) : a.toString().compareTo(b.toString()) < 0 ? a : b; }
    static int rank(IT t){ return t instanceof IT.RCC ? 2 : t instanceof IT.RCX ? 1 : 0; }
    IT meet(IT t1, IT t2){ if (t2 instanceof IT.U || t1.equals(t2)){ return t1; } if (t1 instanceof IT.U){ return t2; }
      if (t1 instanceof IT.ReadImmX(var x1) && x1.equals(t2)){ return t1; } if (t2 instanceof IT.ReadImmX(var x2) && x2.equals(t1)){ return t2; }
      if (t1 instanceof IT.RCC x1 && t2 instanceof IT.RCC x2){ if (!x1.c().name().equals(x2.c().name())){ return leastBad(x1, x2); }
        return x1.withRCTs(meetRcNoH(x1.rc(), x2.rc()), meet(x1.c().ts(), x2.c().ts())); }
      if (!(t1 instanceof IT.RCX x1 && t2 instanceof IT.RCX(var rc2, var x2)) || !x1.x().equals(x2)){ return leastBad(t1, t2); }
      return x1.withRC(meetRcNoH(of(x1.rc()), of(rc2)).get()); } static Optional<RC> meetRcNoH(Optional<RC> a, Optional<RC> b){
      if (a.isEmpty()){ return b; } if (b.isEmpty()){ return a; } var x= noH(a.get()); var y= noH(b.get());
      if (x == y || y == RC.iso || y == RC.read && x != RC.iso){ return of(x); } if (x == RC.iso || x == RC.read){ return of(y); }
      return of(RC.imm); } static RC noH(RC a){ return a == RC.readH ? RC.read : a == RC.mutH ? RC.mut : a; }
    List<IT> meet(List<IT> t1, List<IT> t2){ return zip(t1, t2, this::meet).toList(); }
    List<IT> meet(List<List<IT>> tss){ return tss.stream().reduce(this::meet).get(); } IE nextStar(List<B> bs, IGamma g, IE e){
      if (g.snap().equals(memo.get(e))){ return e; } while (true){ var s= g.snap(); var oe= next(bs, g, e);
        if (oe == e && s.equals(g.snap())){ memo.put(e, s); return e; } e = oe; } }
    List<IE> nextStar(List<B> bs, IGamma g, List<IE> es){ return norm(es, es.stream().map(ei -> nextStar(bs, g, ei)).toList()); }
    List<IE> meetWithTargs(List<IE> es, MSigL m, List<IT> targs){ return norm(es, zip(es, m.ps0(), (e,p) -> meet(e, m.inst(p, targs))).toList()); }
    IE next(List<B> bs, IGamma g, IE e){ return switch (e){ case IE.X x -> { ck(g.notFunnelledInto(x.name()));
          var t1= g.getWithRC(x.name()); var t2= x.t(); if (t1.equals(t2)){ yield x; } if (!(t2 instanceof IT.U)){ updateG(g, x.name(), t2); }
          yield x.withT(meet(t1, t2)); } case Literal l -> nextL(bs, g, l); case IE.Call c when c.written() || c.rc().isPresent() -> nextC(bs, g, c); case IE.Call c -> {
          var ee= nextStar(bs, g, c.e()); var es= nextStar(bs, g, c.es()); if (!(ee.t() instanceof IT.RCC rcc)){ yield c.withEEs(ee, es); }
          var om= methodHeader(rcc, c.name(), empty()); if (om.isEmpty()){ yield c.withEEs(ee, es); } var m= om.get();
          var ts= qMarks(m.methBs().size());
          yield new IE.Call(ee, c.name(), of(m.rc()), ts, meetWithTargs(es, m, ts), false).withT(meet(c.t(), m.inst(m.ret0(), ts))); }
        case IE.Type c -> nextT(c); }; } IT preferred(IT.RCC type){ var d= from(type.c().name());
      var c= d.cs().stream().filter(ci -> ci.name().equals(widen)).findFirst(); if (c.isEmpty()){ return type; }
      var wid= rename(c.get().ts().getFirst(), B.xs(d.bs()), type.c().ts()); if (!(wid instanceof IT.RCC(_, var widC))){ return type; }
      return new IT.RCC(type.rc(), widC); } Optional<IM> methodHeaderIM(IT.RCC rcc, MName name, Optional<RC> favorite){
      var d= from(rcc.c().name()); if (d == null){ return empty(); } var ms= d.ms().stream().filter(m -> m.sig().m().get().equals(name)).toList();
      Function<RC,Optional<IM>> one= rc -> ms.stream().filter(m -> m.sig().rc().get() == rc).findFirst();
      var rc= rcc.rc().map(r -> r == RC.iso ? RC.imm : noH(r)).orElse(RC.imm);
      var order= rc == RC.read ? List.of(RC.read, RC.imm, RC.mut) : rc == RC.mut ? List.of(RC.mut, RC.read, RC.imm) : List.of(RC.imm, RC.read, RC.mut);
      return favorite.map(one).orElseGet(() -> ms.size() == 1 ? of(ms.getFirst()) : order.stream().flatMap(r -> one.apply(r).stream()).findFirst()); }
    Optional<MSigL> methodHeader(IT.RCC rcc, MName name, Optional<RC> favorite){ var d= from(rcc.c().name());
      return methodHeaderIM(rcc, name, favorite).map(m -> new MSigL(m.sig().rc().get(), push(B.xs(d.bs()), B.xs(m.sig().bs().get())), d.bs(), rcc.c().ts(), m.sig().bs().get(), m.sig().ts(), m.sig().ret())); }
    static void updateG(IGamma g, String x, IT t2){ var t1= g.get(x); var t= t1 instanceof IT.U ? t2
        : t1 instanceof IT.RCC(var aRc, var aC) && t2 instanceof IT.RCC(var bRc, var bC) && aC.name().equals(bC.name()) ? new IT.RCC(aRc.isEmpty() ? bRc : bRc.isEmpty() ? aRc : of(glbRcNoH(aRc.get(), bRc.get())), aC)
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
      var fromLiterals= IntStream.range(0, es.size()).filter(i -> es.get(i) instanceof Literal).mapToObj(i -> refine(m.xs(), m.ps0().get(i), es.get(i).t()));
      var hard= meet(Stream.concat(Stream.of(qMarks(written.size())), fromLiterals).toList());
      var fixed= zip(written, hard, (w,h) -> decided(w) ? w : h).toList(); return zip(fixed, all, (b,r) -> decided(b) ? b : r).toList(); }
    static boolean decided(IT t){ return t.isTV() && !(t instanceof IT.RCC(var rc, _) && rc.isEmpty()); } Optional<IT.RCC> preciseSelf(Literal l){
      if (l.infName() && l.rc().isEmpty()){ return empty(); } return of(new IT.RCC(l.rc(), new IT.C(l.name(), toXs(B.xs(l.bs()))))); }
    IE nextL(List<B> bs, IGamma g, Literal l){ var selfPrecise= preciseSelf(l); if (!l.infHead()){ var cs0= l.cs();
        var selfSuper= cs0.size() != 1 ? selfPrecise : selfPrecise.map(p -> new IT.RCC(p.rc(), cs0.getFirst()));
        l = l.infName() ? selfSuper.map(l::withT).orElse(l) : l.withT(selfPrecise.get()); if (!(l.t() instanceof IT.RCC(_, var c))){ return l; }
        l = l.infName() && !c.name().equals(l.name()) ? expandLiteral(l, c, bs) : expandDeclaration(l, true); }
      if (!(l.t() instanceof IT.RCC rcc)){ return l; } var res= new ArrayList<IM>(l.ms().size()); var ts= rcc.c().ts(); for (var mi : l.ms()){
        var rcci= withTsNormBs(rcc, ts); var next= mi.e().isEmpty() ? header(rcci, mi) : nextMStarOp(bs, g, l, selfPrecise, rcci, mi);
        ts = meet(ts, next.ts); res.add(next.m); } var ms= norm(l.ms(), res);
      if (ms == l.ms() && ts.equals(rcc.c().ts())){ return commitToTable(g, bs, l, rcc); } var t= withTsNormBs(rcc, ts);
      return commitToTable(g, bs, l.withMsT(ms, t), t); } IE commitToTable(IGamma g, List<B> bs, Literal l, IT.RCC rcc){ var name= l.name();
      if (!rcc.isTV() || !l.ms().stream().allMatch(m -> m.sig().ret().isTV() && m.sig().ts().stream().allMatch(IT::isTV)) || cache.containsKey(name)){ return l; }
      var localBs= cat(ftvMs(g, l.ms()), ftvCs(l.cs()), rcc.ftv()).distinct().map(x -> B.get(bs, x)).toList(); var newName= name.withArity(localBs.size());
      var ms= name.equals(newName) ? l.ms() : norm(l.ms(), l.ms().stream().map(mi -> !mi.sig().origin().get().equals(name) ? mi : mi.withSig(mi.sig().withOrigin(newName))).toList());
      var orc= l.rc().or(rcc::rc).map(Methods::noH); var orcc= new IT.RCC(orc, rcc.c());
      if (l.ms().stream().allMatch(m -> m.e().isEmpty()) && l.infHead() && from(rcc.c().name()) != null){ return new IE.Type(orcc, preferred(orcc)); }
      var selfInferred= rcc.c().name().equals(l.name());
      var cs= ToCore.distinctTypes(localBs, selfInferred ? fetchCs(rcc.c()) : push(rcc.c(), fetchCs(rcc.c()))); checkMagicSupertypes(l, cs);
      l = new Literal(orc, newName, localBs, cs, l.thisName(), ms, rcc, l.infName(), l.infHead());
      if (selfInferred){ l = l.withT(preciseSelf(l).get()); } register(l); return l; } record TSM(List<IT> ts, IM m){} TSM header(IT.RCC rcc, IM m){
      var sig= m.sig(); var omh= methodHeaderIM(rcc, sig.m().get(), sig.rc()); if (omh.isEmpty()){ return new TSM(rcc.c().ts(), m); }
      var rcc0= withTsNormBs(rcc, refineClsTsFromHeader(rcc, sig, omh.get().sig()));
      return new TSM(dropMethBs(rcc0.c().ts(), B.xs(sig.bs().get())), m.withSig(normalizeSigAgainstHeader(rcc0, sig))); }
    TSM nextMStarOp(List<B> bs, IGamma g, Literal l, Optional<IT.RCC> selfPrecise, IT.RCC rcc, IM m){ var litBs= l.infName() ? bs : l.bs();
      g.fs.add(new IGamma.Frame(m.sig().rc().get(), litBs, new HashMap<>()));
      g.declare(l.thisName(), selfPrecise.<IT>map(s -> new IT.RCC(s.rc().map(RC::isoToMut), s.c())).orElse(IT.U.Instance));
      g.fs.add(new IGamma.Frame(m.sig().rc().get(), litBs, new HashMap<>()));
      for (int i= 0; i < m.xs().size(); i++){ g.declare(m.xs().get(i), m.sig().ts().get(i)); }
      var e= nextStar(push(litBs, m.sig().bs().get()), g, meet(m.e().get(), m.sig().ret()));
      var args= zip(m.xs(), m.sig().ts(), (x,t) -> x.equals("_") ? t : meet(t, g.get(x))).toList(); g.fs.removeLast();
      g.fs.removeLast(); var h= header(rcc, m.withSig(m.sig().withTsT(args, meet(m.sig().ret(), e.t())))); var sig= h.m().sig();
      var e1= meet(e, sig.ret()); return new TSM(h.ts(), sig.equals(m.sig()) && e1 == m.e().get() ? m : new IM(sig, m.xs(), of(e1))); }
    List<IT> refineClsTsFromHeader(IT.RCC rcc, ISig improvedSig, ISig imh){ var Xs= B.xs(from(rcc.c().name()).bs());
      var fromBody= meet(Stream.concat(zip(imh.ts(), improvedSig.ts(), (t,it) -> refine(Xs, t, it)), Stream.of(refine(Xs, imh.ret(), improvedSig.ret()))).toList());
      return zip(rcc.c().ts(), fromBody, this::keepDecided).toList(); } IT keepDecided(IT decided, IT fromBody){
      var decidedIso= decided instanceof IT.RCX(var aRc, _) && aRc == RC.iso;
      if (xName(decided).isPresent() && xName(decided).equals(xName(fromBody)) && !decidedIso){ return decided; }
      if (!(decided instanceof IT.RCC(var aRc, var aC) && fromBody instanceof IT.RCC b)){ return meet(decided, fromBody); }
      if (!aC.name().equals(b.c().name())){ var asDecided= adaptedSuperTs(b, aC.name());
        return asDecided.isEmpty() ? decided : keepDecided(decided, asDecided.getFirst()); }
      return b.withRCTs(aRc.or(b::rc), zip(aC.ts(), b.c().ts(), this::keepDecided).toList()); } ISig normalizeSigAgainstHeader(IT.RCC rcc, ISig improvedSig){
      var h= methodHeader(rcc, improvedSig.m().get(), improvedSig.rc()).get(); var xs= toXs(B.xs(improvedSig.bs().get()));
      return improvedSig.withTsT(h.ps0().stream().map(p -> h.inst(p, xs)).toList(), h.inst(h.ret0(), xs)); }
    List<IT> dropMethBs(List<IT> ts, List<String> methBs){ if (methBs.isEmpty()){ return ts; }
      return ts.stream().map(t -> t instanceof IT.RCC rcc ? withTsNormBs(rcc, dropMethBs(rcc.c().ts(), methBs)) : xName(t).filter(methBs::contains).isPresent() ? IT.U.Instance : t).toList();
    } List<IT> refine(List<String> xs, IT t, IT t1){ if (t1 instanceof IT.U){ return qMarks(xs.size()); } return switch (t){
        case IT.X x -> { var n= xs.indexOf(x.name()); yield IntStream.range(0, xs.size()).<IT>mapToObj(i -> i == n ? t1 : IT.U.Instance).toList(); }
        case IT.RCX(_, var x) -> refine(xs, x, switch (t1){ case IT.RCX(_, var x1) -> x1;
          case IT.ReadImmX(var x1) -> x1; case IT.RCC(_, var c) -> new IT.RCC(empty(), c); default -> t1; });
        case IT.ReadImmX(var x) -> refine(xs, x, t1 instanceof IT.ReadImmX(var x1) ? x1 : t1); case IT.RCC rcc -> propagateXs(xs, rcc, t1);
        case IT.U _ -> qMarks(xs.size()); }; } boolean isASuperB(TName a, TName b){ var d= from(b); return d != null && has(d.cs(), a); }
    List<IT.RCC> adaptedSuperTs(IT.RCC src, TName target){ var d= from(src.c().name()); if (d == null){ return List.of(); }
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
        case Literal l when l.infHead() || !l.infName() || !l.cs().isEmpty() || !(l.t() instanceof IT.U) -> arg;
        case Literal l when !receiver || implementable(exp.c().name()) -> l.withT(new IT.RCC(exp.rc(), new IT.C(exp.c().name(), qMarks(exp.c().ts().size()))));
        case Literal l -> { var res= new Literal(of(RC.imm), l.name(), l.bs(), l.cs(), l.thisName(), l.ms(), true);
          yield res.withT(preciseSelf(res).get()); } default -> arg; }; } boolean implementable(TName head){ var d= from(head);
      if (d == null){ return false; } var foreignForbidden= !head.pkgName().equals(p.name()) && (!head.isPublic() || has(d.cs(), sealed));
      return !foreignForbidden && TypeSystem.hasInstance(d); } static IT normToBound(IT t, EnumSet<RC> allowed){
      if (allowed.size() == 1){ return t.withRC(allowed.iterator().next()); } if (!(t instanceof IT.RCC(var rc, var c))){ return t; }
      if (!(rc.isEmpty() || rc.get() == RC.iso && !allowed.contains(RC.iso))){ return t; }
      return new IT.RCC(allowed.contains(RC.imm) ? empty() : of(RC.read), c); }
    static List<IT> normToBounds(List<B> scope, List<B> bs, List<IT> ts){
      return zip(ts, bs, (ti,bi) -> xName(ti).map(x -> B.get(scope, x).rcs().equals(bi.rcs())).orElse(true) ? normToBound(ti, bi.rcs()) : ti).toList(); }
    static Optional<String> xName(IT t){ return switch (t){ case IT.X x -> of(x.name()); case IT.RCX(_, var x) -> of(x.name());
      case IT.ReadImmX(var x) -> of(x.name()); default -> empty(); };} IT.RCC withTsNormBs(IT.RCC rcc, List<IT> ts){
      var d= from(rcc.c().name()); return d == null ? rcc.withTs(ts) : rcc.withTs(zip(ts, d.bs(), (ti,bi) -> normToBound(ti, bi.rcs())).toList()); } 
  }
  record ToCore(List<B> ctx){ IE of(IE exp, IE orig){ return switch (exp){ case IE.X(var name, _) -> new IE.X(name);
      case IE.Type(var type, _) -> new IE.Type((IT.RCC)norm(type)); case Literal le -> literal(le, (Literal)orig); case IE.Call e -> { var o= (IE.Call)orig;
        yield new IE.Call(of(e.e(), o.e()), e.name(), Optional.of(e.rc().orElse(RC.imm)), (o.targs().isEmpty() ? e.targs() : o.targs()).stream().map(Frontend::norm).toList(), zip(e.es(), o.es(), this::of).toList(), false);
      } };} Literal literal(Literal e, Literal o){ var bs= e.bs(); if (e.infName() && bs.isEmpty()){ var g= new IGamma();
        bs = cat(ftvCs(e.cs()), ftvMs(g, e.ms()), ftvMs(g, o.ms())).distinct().map(x -> B.get(ctx, x)).toList(); } var name= e.name().withArity(bs.size());
      var inner= new ToCore(e.infName() ? push(ctx, bs).stream().distinct().toList() : bs);
      var ms= e.ms().stream().map(me -> inner.m(me, me.e().isEmpty() ? me : o.ms().get(me.sig().idx())))
        .map(m -> !m.sig().origin().get().equals(e.name()) ? m : m.withSig(m.sig().withOrigin(name))).toList();
      var cs= distinctTypes(inner.ctx(), o.cs().isEmpty() ? e.cs() : push(o.cs(), e.cs())).stream().map(Frontend::normC).toList();
      return new Literal(Optional.of(e.rc().orElse(RC.imm)), name, bs, cs, e.thisName(), ms, e.infName()); }
    static List<IT.C> distinctTypes(List<B> bs, List<IT.C> cs){ var res= new ArrayList<IT.C>();
      for (var c : cs){ if (res.stream().noneMatch(r -> TypeSystem.eqModXRC(bs, norm(new IT.RCC(Optional.of(RC.imm), r)), norm(new IT.RCC(Optional.of(RC.imm), c))))){ res.add(c); } }
      return res; } IM m(IM e, IM o){ var s= sig(e.sig(), o.sig());
      return new IM(s, e.xs(), e.e().map(ei -> new ToCore(push(ctx, s.bs().get()).stream().distinct().toList()).of(ei, o.e().get()))); }
    static ISig sig(ISig inf, ISig usr){ var ts= zip(usr.ts(), inf.ts(), (u,i) -> u instanceof IT.U ? i : u).toList();
      return new ISig(usr.rc().or(inf::rc).orElse(RC.imm), usr.m().or(inf::m).orElse(new MName(".inferenceFailed", ts.size())), usr.bs().or(inf::bs).orElse(List.of()),
        ts.stream().map(Frontend::norm).toList(), norm(usr.ret() instanceof IT.U ? inf.ret() : usr.ret()), usr.origin().or(inf::origin).orElse(inferUnknown), usr.abs(), usr.idx()); } }
  record Gamma(Gamma tail, String name, IT current){ static final Gamma empty= new Gamma(null, null, null);
    Gamma add(String name, IT t){ return new Gamma(this, name, t); }
    Gamma map(UnaryOperator<IT> f){ return this == empty ? this : new Gamma(tail.map(f), name, current == null ? null : f.apply(current)); }
    IT bind(String x){ return this == empty ? null : name.equals(x) ? current : tail.bind(x); }
    Gamma filterFTV(Literal l, boolean captureFree){
      if (this == empty){ return this; } var rest= tail.filterFTV(l, captureFree);
      var drop= captureFree || current != null && !current.ftv().allMatch(B.xs(l.bs())::contains);
      return new Gamma(rest, name, drop ? null : current); } }
  record MType(RC rc, List<IT> ts, IT t){} enum Mode{
    useRead(iso, readH, mutH, readH), flexy(iso, imm, mutH, readH), hyg(mutH, readH, mutH, readH), strong(iso, imm, iso, imm); final RC m, r, mh, rh;
    Mode(RC m, RC r, RC mh, RC rh){ this.m= m; this.r= r; this.mh= mh; this.rh= rh; }
    RC of(RC rc){ return switch (rc){ case mut -> m; case read -> r; case mutH -> mh; case readH -> rh; default -> rc; }; } }
  record TypeSystem(Function<TName,Literal> decs){ static void allOk(List<Literal> tops, Map<TName,Literal> other){ var map= new HashMap<TName,Literal>();
      tops.forEach(t -> collect(t, map)); var ts= new TypeSystem(n -> from(n, map::get, other)); tops.forEach(l -> ts.litOk(Gamma.empty, l)); }
    static void collect(IE e, HashMap<TName,Literal> map){ if (e instanceof Literal l){ map.put(l.name(), l); } e.children().forEach(c -> collect(c, map)); }
    boolean kindOf(List<B> bs, IT t, EnumSet<RC> allowed){ if (!allowed.containsAll(intrinsicRCs(bs, t))){ return false; }
      if (!(t instanceof IT.RCC(_, var c))){ return true; } var params= decs.apply(c.name()).bs();
      return zip(c.ts(), params, (ti,p) -> kindOf(bs, ti, p.rcs())).allMatch(v -> v); }
    void kind(List<B> bs, IT t){ kind(bs, t, EnumSet.allOf(RC.class)); } void kind(List<B> bs, IT t, EnumSet<RC> allowed){ ck(!kindOf(bs, t, allowed)); }
    static EnumSet<RC> intrinsicRCs(List<B> bs, IT t){ return switch (t){ case IT.RCC(var rc, _) -> EnumSet.of(rc.get());
      case IT.RCX(var rc, _) -> EnumSet.of(rc); case IT.X(var x) -> B.get(bs, x).rcs(); case IT.U _ -> throw new Fail(); case IT.ReadImmX(var x) -> {
        var rcs= intrinsicRCs(bs, x);
        yield EnumSet.of(iso, imm).containsAll(rcs) ? EnumSet.of(imm) : EnumSet.of(mut, mutH, read, readH).containsAll(rcs) ? EnumSet.of(read) : EnumSet.of(read, imm);
      } };} Gamma vpaOf(Gamma g, Literal l, IM m){
      return g.map(t -> { if (m.sig().rc().get() == imm || kindOf(l.bs(), t, EnumSet.of(iso, imm))){ return t.withRC(imm); } if (m.sig().rc().get() == read){
          if (t.explicitRC().stream().anyMatch(r -> r == mut || r == read)){ return t.withRC(read); }
          if (t instanceof IT.X || t instanceof IT.ReadImmX){ return t.readImm(); } }
        return kindOf(l.bs(), t, EnumSet.of(imm, mut, read)) ? t : t.readImm(); }); } Gamma discard(Gamma g, Literal l){
      return g.map(t -> { var drop= !kindOf(l.bs(), t, EnumSet.allOf(RC.class)) || !kindOf(l.bs(), t, EnumSet.of(iso, imm, mut, read)) || l.rc().get().isIsoOrImm() && !kindOf(l.bs(), t, EnumSet.of(iso, imm));
        return drop ? null : t; }); } boolean isSub(List<B> bs, IT t1, IT t2){ return t1.equals(t2)
        || t2 instanceof IT.ReadImmX(var x2) && t1 instanceof IT.X x && x2.name().equals(x.name()) && kindOf(bs, x, EnumSet.of(iso, imm, mut, read))
        || isSameShapeSubtype(bs, t1, t2)
        || t1 instanceof IT.RCC(var rc1, var c1) && decs.apply(c1.name()).cs().stream().anyMatch(ci -> isSub(bs, rename(new IT.RCC(rc1, ci), B.xs(decs.apply(c1.name()).bs()), c1.ts()), t2));
    } List<IT> typeOf(List<B> bs, Gamma g, IE e, List<IT> rs){ return switch (e){ case IE.X x -> {
        var t= g.bind(x.name()); ck(t == null); yield reqs(bs, t, rs, false); } case IE.Type t -> {
        kind(bs, t.type()); var ll= decs.apply(t.type().c().name()); ck(!hasInstance(ll)); var rc= t.type().rc().get();
        var getIso= (rc.isReadOrImm() && !hasAbstractMut(ll)) || rc == mut || rc == mutH; var l= ll.withRC(getIso ? iso : rc);
        l.ms().forEach(m -> checkImplemented(l, m)); yield reqs(bs, getIso ? t.type().withRC(iso) : t.type(), rs, true); }
      case Literal l -> checkLiteral(bs, g, l, rs); case IE.Call c -> callTyping(bs, g, c, rs); };}
    static boolean hasInstance(Literal l){ return l.thisName().equals("this") || has(l.cs(), captureFree); }
    static long count(String x, IE e, boolean active){ var here= e instanceof IE.X v && v.name().equals(x) ? 1 : 0;
      if (active && e instanceof Literal){ return here; } return here + e.children().mapToLong(c -> count(x, c, active)).sum(); }
    static boolean hasAbstractMut(Literal l){ return l.ms().stream().anyMatch(m -> m.sig().abs() && m.sig().rc().get() == mut); }
    List<IT> reqs(List<B> bs, IT got, List<IT> rs, boolean rccOnly){ if (rs.isEmpty()){ return List.of(got); }
      ck(rccOnly && rs.stream().anyMatch(r -> !(r instanceof IT.RCC))); return rs.stream().map(r -> isSub(bs, got, r) ? got : null).toList(); }
    List<IT> checkLiteral(List<B> bs1, Gamma g, Literal _l, List<IT> rs){ var selfNamed= !_l.thisName().equals("_");
      var getIso= ((_l.rc().get().isReadOrImm() && !hasAbstractMut(_l) && !selfNamed) || _l.rc().get() == mut) && captureFree(_l.bs(), g.filterFTV(_l, has(_l.cs(), captureFree)), _l);
      var l= getIso ? _l.withRC(iso) : _l;
      ck(rs.stream().anyMatch(r -> !(r instanceof IT.RCC)));
      ck(l.ms().stream().anyMatch(m -> m.sig().origin().get().equals(inferUnknown)) || l.cs().stream().anyMatch(c -> c.ts().stream().anyMatch(TypeSystem::mentionsInferUnknown)));
      var thisType= new IT.RCC(l.rc(), new IT.C(l.name(), toXs(B.xs(l.bs())))); kind(bs1, thisType); litOk(discard(g.filterFTV(l, has(l.cs(), captureFree)), l), l);
      ck(selfNamed && count(_l.thisName(), _l, false) == 0); ck(l.ms().stream().anyMatch(m -> m.e().isPresent() && !hasInstance(l) && !callable(l.rc().get(), m.sig().rc().get())));
      l.ms().forEach(m -> checkImplemented(l, m)); return reqs(bs1, thisType, rs, false); }
    static boolean captureFree(List<B> bs, Gamma g, IE e){ if (!(e instanceof IE.X x)){ return e.children().allMatch(c -> captureFree(bs, g, c)); }
      return g.bind(x.name()) == null || intrinsicRCs(bs, g.bind(x.name())).stream().allMatch(RC::isIsoOrImm); }
    static boolean mentionsInferUnknown(IT t){ return t instanceof IT.RCC(_, var c) && (c.name().equals(inferUnknown) || c.ts().stream().anyMatch(TypeSystem::mentionsInferUnknown)); }
    void checkImplemented(Literal l, IM m){ ck(m.sig().abs() && callable(l.rc().get(), m.sig().rc().get())); }
    static boolean callable(RC litRC, RC recRc){ return recRc != mut || !litRC.isReadOrImm(); } void litOk(Gamma g, Literal l){
      if (has(l.cs(), baseId)){ var m= l.ms().getFirst(); var isId= switch (m.e().orElse(null)){ case null -> true;
          case IE.X(var name, _) -> name.equals(m.xs().getFirst());
          case IE.Call c -> c.e() instanceof IE.X(var recv, _) && recv.equals(m.xs().getFirst()) && c.name().equals(new MName(".as", 1))
            && m.sig().ts().getFirst() instanceof IT.RCC(_, var cc) && has(decs.apply(cc.name()).cs(), baseContainer); default -> false; }; ck(!isId); }
      var delta= l.bs(); for (var c : l.cs()){ kind(delta, new IT.RCC(of(imm), c)); ck(!hasInstance(decs.apply(c.name()))); } var sources= new ArrayList<ISig>();
      for (var parent : l.cs()){ var parentDef= decs.apply(parent.name()); for (var m : parentDef.ms()){
          if (!m.sig().origin().get().equals(parentDef.name())){ continue; } var s= m.sig(); var canonical= findCanonical(l, s.m().get(), s.rc().get()).bs().get();
          var mapXs= B.xs(push(s.bs().get(), parentDef.bs())); var mapTs= push(toXs(B.xs(canonical)), parent.ts());
          sources.add(new ISig(s.rc(), s.m(), of(canonical), renameIT(s.ts(), mapXs, mapTs), rename(s.ret(), mapXs, mapTs), s.origin(), s.abs(), s.idx()));
        } } for (var m : l.ms()){ if (m.sig().origin().get().equals(l.name())){ sources.add(m.sig()); } }
      sources.stream().collect(Collectors.groupingBy(s -> new RCMName(s.rc(), s.m().get()), LinkedHashMap::new, Collectors.toList()))
        .forEach((k,group) -> { var chosen= findCanonical(l, k.name(), k.rc().get()); var ctx= push(l.bs(), chosen.bs().get()); for (var s : group){
          for (int i= 0; i < chosen.ts().size(); i++){ ck(!sameOuterRC(ctx, chosen.ts().get(i), s.ts().get(i)) || !isSub(ctx, s.ts().get(i), chosen.ts().get(i))); }
          ck(!sameOuterRC(ctx, chosen.ret(), s.ret()) || !isSub(ctx, chosen.ret(), s.ret())); } });
      var g1= g.add(l.thisName(), new IT.RCC(of(l.rc().get().isoToMut()), new IT.C(l.name(), toXs(B.xs(delta))))); for (var m : l.ms()){ var g2= vpaOf(g1, l, m);
        var allBs= push(delta, m.sig().bs().get()); m.sig().ts().forEach(t -> kind(allBs, t)); kind(allBs, m.sig().ret()); if (m.e().isEmpty()){ continue; }
        for (int i= 0; i < m.xs().size(); i++){ g2 = g2.add(m.xs().get(i), m.sig().ts().get(i)); } ck(typeOf(allBs, g2, m.e().get(), List.of(m.sig().ret())).getFirst() == null);
        for (int i= 0; i < m.xs().size(); i++){ var x= m.xs().get(i); if (kindOf(allBs, m.sig().ts().get(i), EnumSet.of(mut, read, mutH, readH, imm))){ continue; }
          ck(count(x, m.e().get(), true) > 0 && count(x, m.e().get(), false) != 1); }
      } } static ISig findCanonical(Literal l, MName name, RC rc){ return l.ms().stream().map(IM::sig).filter(s -> s.m().get().equals(name) && s.rc().get() == rc).findFirst().get(); }
    static boolean isSameShapeSubtype(List<B> bs, IT t1, IT t2){
      if (!eqModXRC(bs, t1.withRC(mut), t2.withRC(mut))){ return false; } var rcs2= intrinsicRCs(bs, t2);
      return intrinsicRCs(bs, t1).stream().allMatch(r1 -> rcs2.stream().allMatch(r1::isSubType)); } static boolean sameOuterRC(List<B> bs, IT a, IT b){
      return (a instanceof IT.ReadImmX) == (b instanceof IT.ReadImmX) && a.explicitRC().equals(b.explicitRC()) || eqModXRC(bs, a, b); }
    static boolean eqModXRC(List<B> bs, IT a, IT b){ if (a.equals(b)){ return true; }
      if (!(a instanceof IT.RCC(var aRc, var aC) && b instanceof IT.RCC(var bRc, var bC))){
        if (!(a.withRC(imm) instanceof IT.RCX(_, var x)) || !a.withRC(imm).equals(b.withRC(imm))){ return false; }
        return B.get(bs, x.name()).rcs().size() == 1 && intrinsicRCs(bs, a).equals(intrinsicRCs(bs, b)); }
      return aRc.equals(bRc) && aC.name().equals(bC.name()) && zip(aC.ts(), bC.ts(), (x,y) -> eqModXRC(bs, x, y)).allMatch(v -> v); }
    List<IT> callTyping(List<B> bs, Gamma g, IE.Call c, List<IT> rs){
      if (!(typeOf(bs, g, c.e(), List.of()).getFirst() instanceof IT.RCC rcc0)){ throw new Fail(); } var d= decs.apply(rcc0.c().name());
      var sig= d.ms().stream().map(IM::sig).filter(s -> s.m().get().equals(c.name()) && s.rc().equals(c.rc())).findFirst().orElseThrow(Fail::new);
      ck(sig.bs().get().size() != c.targs().size()); for (int i= 0; i < c.targs().size(); i++){ kind(bs, c.targs().get(i), sig.bs().get().get(i).rcs()); }
      var xs= B.xs(push(d.bs(), sig.bs().get())); var ts0= push(rcc0.c().ts(), c.targs());
      var base= new MType(sig.rc().get(), renameIT(sig.ts(), xs, ts0), rename(sig.ret(), xs, ts0));
      var app= promotions(bs, base).stream().filter(m -> rcc0.rc().get().isSubType(m.rc())).toList(); ck(app.isEmpty());
      var okByArg= new ArrayList<List<Integer>>(); for (int argi= 0; argi < c.es().size(); argi++){ var ai= argi;
        var reqs= app.stream().map(m -> m.ts().get(ai)).distinct().toList(); var resByReq= typeOf(bs, g, c.es().get(argi), reqs);
        ck(resByReq.stream().allMatch(Objects::isNull));
        okByArg.add(IntStream.range(0, app.size()).filter(i -> resByReq.get(reqs.indexOf(app.get(i).ts().get(ai))) != null).boxed().toList()); }
      var possible= IntStream.range(0, app.size()).boxed().filter(ci -> okByArg.stream().allMatch(ok -> ok.contains(ci))).toList(); ck(possible.isEmpty());
      if (rs.isEmpty()){ return List.of(bestUnique(bs, app, possible)); } return rs.stream().map(req -> {
        var okRet= possible.stream().filter(i -> isSub(bs, app.get(i).t(), req)).toList();
        return okRet.isEmpty() ? null : bestUnique(bs, app, okRet); }).toList(); }
    IT bestUnique(List<B> bs, List<MType> app, List<Integer> idxs){ var all= idxs.stream().map(i -> app.get(i).t()).toList();
      return all.stream().filter(ti -> all.stream().noneMatch(tj -> !tj.equals(ti) && isSub(bs, tj, ti))).findFirst().get(); }
    static RC lub(EnumSet<RC> rcs){ return bound(rcs, RC::isSubType); } static RC glb(EnumSet<RC> rcs){ return bound(rcs, (a,b) -> b.isSubType(a)); }
    static RC bound(EnumSet<RC> rcs, BiPredicate<RC,RC> le){ var bs= Stream.of(RC.values()).filter(b -> rcs.stream().allMatch(x -> le.test(x, b))).toList();
      return bs.stream().filter(b -> bs.stream().allMatch(o -> le.test(b, o))).findFirst().get(); } static List<MType> promotions(List<B> d, MType m){
      var out= new LinkedHashSet<MType>(List.of(m, apply(d, m, Mode.flexy, _ -> Mode.flexy, Mode.flexy), apply(d, m, Mode.strong, _ -> Mode.strong, Mode.strong),
        apply(d, m, Mode.useRead, _ -> Mode.useRead, Mode.hyg), apply(d, m, Mode.hyg, _ -> Mode.flexy, Mode.hyg)));
      for (int i= 0; i < m.ts().size(); i++){ var ii= i; out.add(apply(d, m, Mode.flexy, j -> j == ii ? Mode.hyg : Mode.flexy, Mode.hyg)); } return List.copyOf(out); }
    static MType apply(List<B> d, MType m, Mode rcM, IntFunction<Mode> tsM, Mode retM){
      return new MType(rcM.of(m.rc()), IntStream.range(0, m.ts().size()).mapToObj(j -> modeF(d, m.ts().get(j), tsM.apply(j), TypeSystem::glb)).toList(), modeF(d, m.t(), retM, TypeSystem::lub)); }
    static IT modeF(List<B> d, IT t, Mode mode, Function<EnumSet<RC>,RC> f){ return switch (t){ case IT.RCC rcc -> rcc.withRC(mode.of(rcc.rc().get()));
        case IT.RCX rcx -> rcx.withRC(mode.of(rcx.rc())); case IT.X x -> modeVar(d, x, rc -> rc, mode, f, t);
        case IT.ReadImmX(var x) -> modeVar(d, x, RC::readImm, mode, f, t); case IT.U _ -> t; }; }
    static IT modeVar(List<B> d, IT.X x, UnaryOperator<RC> inst, Mode mode, Function<EnumSet<RC>,RC> f, IT original){ var rcs= EnumSet.noneOf(RC.class);
      B.get(d, x.name()).rcs().forEach(rc -> rcs.add(inst.apply(rc))); if (rcs.stream().allMatch(rc -> mode.of(rc) == rc)){ return original; }
      var mapped= EnumSet.noneOf(RC.class); rcs.forEach(rc -> mapped.add(mode.of(rc))); return new IT.RCX(f.apply(mapped), x); } } }
