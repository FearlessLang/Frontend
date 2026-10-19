package compact;
import static compact.Frontend.TK.*;
import static compact.Frontend.RC.*;
import static compact.Frontend.Mode.*;
import static compact.Util.*;
import static java.util.Optional.*;
import compact.Frontend.IT.*;
import compact.Frontend.IE.Call;
import compact.Frontend.IE.Type;
import java.math.*;
import java.util.*;
import java.util.function.*;
import java.util.regex.Pattern;
import java.util.stream.*;
public final class Frontend{ @SuppressWarnings("serial") public static final class Fail extends RuntimeException{} static void ck(boolean b){ if (b){ throw new Fail(); } }
  public static Object parse(String input){ return new Parser(new Names(list(), list(), list(), null), tokens(input)).parseAll(Parser::parseFileFull); }
  public static List<Literal> compile(String pkgName, Map<String,String> override, Map<String,String> files, List<Literal> otherLits){
    var other= otherLits.stream().collect(Collectors.toMap(Literal::name, d -> d)); var raw= new TreeMap<String,FileFull>();
    files.forEach((path, content) -> raw.put(path, (FileFull)parse(content)));
    var heads= filter(raw.keySet(), p -> p.matches("(.*/)?_rank_[^/]*\\.[^/]*"));
    ck(heads.size() != 1); var head= raw.get(heads.getFirst());
    ck(any(raw.values(), f -> f != head && !(f.maps.isEmpty() && f.uses.isEmpty())));
    var ds= flat(raw.values(), f -> f.decs.stream()); var uses= map(head.uses, FileFull.Use::out);
    var decNames= flat(ds, d -> d.owner.decs.stream()); ck(dup(decNames)); var decStrs= map(decNames, TName::s);
    ck(!Collections.disjoint(decStrs, uses)); ck(ds.stream().flatMap(d -> d.owner.gen.used.stream()).anyMatch(x -> decStrs.contains(x) || uses.contains(x)));
    var map= new HashMap<>(override); for (var u : head.uses){ var p= map.getOrDefault(u.in.pkgName(), u.in.pkgName());
      var in= p + "." + u.in.simpleName(); map.put(u.out, in);
      var dom= p.equals(pkgName) ? decNames.stream().map(n -> n.withPkgName(pkgName)) : other.keySet().stream();
      ck(dom.noneMatch(e -> e.s.equals(in))); } var ctx= new Methods(new Pkg(pkgName, map, ds, new HashSet<>(decNames)), other);
    var res= ctx.steps(ctx.headers(toInference(ctx))); TypeSystem.allOk(res, other); return res; } public enum RC{
    imm, mut, read, iso, mutH, readH; boolean isSubType(RC other){ return this == other || other == readH || this == iso || other == read && !isH() || this == mut && other == mutH; }
    boolean isH(){ return this == mutH || this == readH; } boolean isReadOrImm(){ return this == read || this == imm; }
    boolean isIsoOrImm(){ return this == iso || this == imm; } RC isoToMut(){ return this == iso ? mut : this; }
    RC readImm(){ return isIsoOrImm() ? imm : read; } } public record TName(String s, int arity){
    static int pkgDot(String s){ return Character.isLowerCase(s.charAt(0)) ? s.indexOf('.') : -1; }
    TName withPkgName(String pkg){ return new TName(pkg+"."+s, arity); }
    TName withArity(int arity){ return new TName(s, arity); }
    String pkgName(){ var i= pkgDot(s); return i == -1 ? "" : s.substring(0, i); }
    String simpleName(){ var i= pkgDot(s); return i == -1 ? s : s.substring(i + 1); } boolean isPublic(){ return !simpleName().startsWith("_"); } }
  public record MName(String s, int arity){ MName withArity(int arity){ return new MName(s, arity); } }
  public record B(String x, EnumSet<RC> rcs){ static List<String> xs(List<B> bs){ return map(bs, B::x); }
    static B get(List<B> bs, String name){ return find(bs, b -> b.x.equals(name)).get(); } }
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
  static boolean isKind(String input, TK... kinds){ return any(list(kinds), k -> k.match(input, 0) == input.length()); }
  static final TK[] typeName= {UppercaseId, SignedFloat, UnSignedFloat, SignedInt, UnsignedInt, SStr, UStr};
  record Token(TK kind, String content, List<Token> tokens){ boolean is(TK... kinds){ return list(kinds).contains(kind); } }
  static final String allowed= "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>,.;:()[]{}`'\"!?@#$%^&_|~\\ \n";
  static final Map<TK,Map<TK,TK>> groups= Map.of(_SOF, Map.of(_EOF, _EOF), ORound, Map.of(CRound, _RoundGroup), OSquareArg, Map.of(CSquare, _SquareGroup), OCurly, Map.of(CCurly, _CurlyGroup, CCurlyId, _CurlyGroup));
  static List<Token> tokens(String s){ s = s.replaceFirst("^\\uFEFF", "").replaceAll("[\\r\\u2028\\u2029\\u0085]", "\n");
    ck(s.codePoints().anyMatch(c -> allowed.indexOf(c) < 0)); var res= new ArrayList<Token>(list(new Token(_SOF, "", list()))); for (int i= 0; i < s.length();){
      TK best= null; int len= 0; for (var k : TK.values()){ var l= k.match(s, i); if (l > len){ best= k; len= l; } } ck(best == null);
      var t= new Token(best, s.substring(i, i+len), list()); i += len; if (t.is(Ws, LineComment, BlockComment)){ continue; }
      ck(t.is(BadSStrQuote) || t.is(OSquareArg) && res.getLast().is(SStr, UStr, SignedInt, UnsignedInt, SignedFloat, UnSignedFloat)); res.add(t); }
    res.add(new Token(_EOF, "", list())); var it= res.iterator(); return tree(it, it.next()).tokens; } static Token tree(Iterator<Token> it, Token open){
    var out= new ArrayList<Token>(list(open)); while (true){ var c= it.next();
      var g= groups.get(open.kind).get(c.kind); if (g != null){ out.add(c); return new Token(g, "", out); }
      if (groups.containsKey(c.kind)){ out.add(tree(it, c)); continue; } ck(any(groups.values(), m -> m.containsKey(c.kind))); out.add(c); } }
  sealed interface PE{ record X(String name) implements PE{}
    record Lit(Optional<String> thisName, List<PM> ms) implements PE{} record TypedLiteral(RC rc, C c, Optional<Lit> l) implements PE{}
    record DeclarationLiteral(Optional<RC> rc, Declaration dec) implements PE{} record CallSquare(Optional<RC> rc, List<IT> ts){}
    record Call(PE e, MName name, Optional<CallSquare> targs, Optional<XPat> pat, List<PE> es) implements PE{} record Implicit() implements PE{} }
  record PSig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Parameter> ps, Optional<IT> t){}
  record PM(Optional<PSig> sig, Optional<PE> body, boolean hasImplicit){
    PM(Optional<PSig> sig, Optional<PE> body){ this(sig, body, body.stream().anyMatch(Frontend::hasImplicit)); }
    int arity(){ return sig.map(s -> s.ps.size()).orElse(0) + (hasImplicit ? 1 : 0); } } static boolean hasImplicit(PE e){ return switch (e){
    case PE.X _, PE.TypedLiteral _, PE.DeclarationLiteral _, PE.Lit _ -> false; case PE.Implicit _ -> true;
    case PE.Call c -> hasImplicit(c.e) || any(c.es, Frontend::hasImplicit); };} record Parameter(Optional<XPat> xp, Optional<IT> t){}
  sealed interface XPat{ Stream<String> parameterNames();
    record Name(String x) implements XPat{ @Override public Stream<String> parameterNames(){ return Stream.of(x); } }
    record Destruct(List<List<MName>> extract, String id) implements XPat{
      @Override public Stream<String> parameterNames(){ return extract.stream().map(e -> e.getLast().s.substring(1) + id); } } }
  record Declaration(TName name, List<B> bs, List<C> cs, PE.Lit l, Owner owner){}
  record FileFull(List<String> maps, List<Use> uses, List<Declaration> decs){ record Use(TName in, String out){} }
  record Names(List<String> xs, List<String> Xs, List<String> hiddenXs, Owner owner){ Names add(List<String> xs, List<String> Xs){
      owner.vars.used.addAll(xs); owner.gen.used.addAll(Xs); return new Names(push(this.xs, xs), push(this.Xs, Xs), hiddenXs, owner); } }
  record RCMName(Optional<RC> rc, MName name){} static final class Parser{ Names names; final List<Token> ts; int index= 0; int limit;
    Parser(Names names, List<Token> ts){ this.names= names; this.ts= ts; limit= ts.size(); }
    Parser make(List<Token> tokens){ return new Parser(names, tokens); } <R> R parseAll(Function<Parser,R> r){ var res= r.apply(this); ck(!end()); return res; }
    boolean end(){ return limit == index; }
    boolean peek(int la, TK... kinds){ return index+la < limit && ts.get(index+la).is(kinds); }
    boolean peek(TK... kinds){ return peek(0, kinds); } boolean peekIf(Predicate<Token> p){ return !end() && p.test(ts.get(index)); }
    Token expect(TK... kinds){ ck(end()); var t= ts.get(index++); ck(kinds.length > 0 && !t.is(kinds)); return t; }
    Token expectLast(TK... kinds){ ck(!ts.get(limit - 1).is(kinds)); limit -= 1; return ts.get(limit); }
    boolean fwdIf(boolean v){ if (v){ index += 1; } return v; } <R> R parseGroup(Function<Parser,R> r){
      var p= make(ts.get(index++).tokens); p.index= 1; p.limit -= 1; return p.parseAll(r); } Parser front(ToIntFunction<Parser> probe){
      var sp= make(ts.subList(index, limit)); int drop= probe.applyAsInt(sp); var res= make(ts.subList(index, index+sp.index-drop)); index += sp.index; return res; }
    <R> List<R> splitBy(ToIntFunction<Parser> probe, Function<Parser,R> elem){ var res= new ArrayList<R>(); while (!end()){ res.add(front(probe).parseAll(elem)); } return res; }
    <R> List<R> parseGroupSep(Function<Parser,R> r, ToIntFunction<Parser> probe){ return parseGroup(p -> p.splitBy(probe, r)); }
    <R> Optional<R> parseFront(ToIntFunction<Parser> probe, Function<Parser,R> first){ var i= index; var p= front(probe); if (!end()){ return of(p.parseAll(first)); } index = i; return empty(); }
    int splitOn(int mode, TK k){ while (!end()){ if (!expect().is(k)){ continue; } if (mode == 2){ index -= 1; } return mode & 1; } return 0; }
    PE parseE(){ var e= parseAtom(); while (!end()){ e = parsePost(e); } return e; }
    boolean isDec(){ return peek(typeName) && (peek(1, Colon) || peek(1, _SquareGroup) && peek(2, Colon)); }
    PE parseAtom(){ if (peek(LowercaseId)){ var x= expect().content; ck(!names.xs.contains(x)); return new PE.X(x); }
      if (peek(_RoundGroup)){ return parseGroup(Parser::parseE); }
      if (peek(ColonColon)){ expect(); return new PE.Implicit(); } if (peek(_CurlyGroup)){ return parseGroup(p -> p.parseLiteral(false)); }
      var rc= parseOptRC(); ck(rc.stream().anyMatch(RC::isH)); if (isDec()){ return new PE.DeclarationLiteral(rc, parseDeclaration(false)); }
      return new PE.TypedLiteral(rc.orElse(imm), parseC(), parseIf(peek(_CurlyGroup), () -> parseGroup(p -> p.parseLiteral(false)))); }
    RC parseRC(){ return RC.valueOf(expect(RCap).content); } Optional<RC> parseOptRC(){ return parseIf(peek(RCap), this::parseRC); } C parseC(){
      var c= parseTName(); if (!peek(_SquareGroup)){ return new C(c, list()); } var ts= parseGroupSep(Parser::parseT, commaSkip);
      return new C(c.withArity(ts.size()), ts); } TName parseTName(){ var s= expect(typeName).content;
      ck(names.Xs.contains(s) || names.hiddenXs.contains(s)); var res= new TName(s, 0); ck(!res.pkgName().isEmpty() && !res.isPublic()); return res; }
    IT parseT(){ if (fwdIf(peek(ReadImm))){ return new ReadImmX(parseTX(false)); } var rc= parseOptRC();
      if (peekIf(t -> t.is(typeName) && !names.Xs.contains(t.content))){ return new RCC(of(rc.orElse(imm)), parseC()); }
      var res= parseTX(false); return rc.map(r -> (IT)new RCX(r, res)).orElse(res); } X parseTX(boolean mustNew){
      var c= expectValidate(UppercaseId, _XId).content; ck(mustNew ? names.Xs.contains(c) || names.hiddenXs.contains(c) : !names.Xs.contains(c));
      return new X(c); } PE parsePost(PE receiver){ if (peek(SignedFloat, SignedInt)){ var num= expect().content;
        var lit= new PE.TypedLiteral(imm, new C(new TName(num.substring(1), 0), list()), empty());
        return new PE.Call(receiver, new MName(num.substring(0, 1), 1), empty(), empty(), list(lit)); }
      var m= new MName(expect(DotName, Op).content, 0); var sq= parseIf(peek(_SquareGroup), () -> parseGroup(Parser::parseCallSquare));
      if (peek(_RoundGroup)){ var es= parseGroupSep(Parser::parseE, Parser::onCommaExp);
        return new PE.Call(receiver, m.withArity(es.size()), sq, empty(), es); }
      var xpat= parseIf(peek(LowercaseId, _CurlyGroup) && peek(1, Eq), () -> { var r= parseXPat(); index += 1; return r; });
      if (end() || peek(DotName, Op, Colon)){ ck(xpat.isPresent()); return new PE.Call(receiver, m, sq, xpat, list()); }
      var atom= parseAtom(); var xs= xsOf(xpat).toList(); checkNewXs(xs);
      ck(xpat.isPresent() && xpat.get() instanceof XPat.Destruct && xs.size() > 31); names = names.add(xs, list());
      if (xpat.isEmpty()){ return new PE.Call(receiver, m.withArity(1), sq, xpat, list(atom)); } var chain= parsePost(new PE.X(""));
      while (!end()){ chain = parsePost(chain); } return new PE.Call(receiver, m.withArity(2), sq, xpat, list(atom, chain)); } XPat parseXPat(){
      if (peek(LowercaseId, Underscore)){ return new XPat.Name(parseDecX().name); } return parseGroup(Parser::parseDestruct); } XPat.Destruct parseDestruct(){
      var id= ts.get(limit).content.substring(1);
      var chains= splitBy(commaSkip, p -> p.splitBy(q -> { q.expect(); return 0; }, q -> new MName(q.expect(DotName).content, 0)));
      ck(chains.isEmpty() || any(chains, List::isEmpty)); var res= new XPat.Destruct(chains, id);
      ck(res.parameterNames().anyMatch(x -> !isKind(x, LowercaseId) || isKind(x, RCap))); return res; } PE.CallSquare parseCallSquare(){
      var hasRC= peek(RCap) && ts.get(index+1).is(Comma, CSquare); var rc= parseIf(hasRC, this::parseRC);
      if (hasRC && !end()){ expect(Comma); } return new PE.CallSquare(rc, splitBy(commaSkip, Parser::parseT)); } PE.X parseDecX(){
      var x= expect(LowercaseId, Underscore).content; ck(names.xs.contains(x)); return new PE.X(x); } PE.Lit parseLiteral(boolean top){
      ck(ts.get(limit).is(CCurlyId)); var thisName= parseIf(fwdIf(peek(SQuote)), () -> parseDecX().name); var n= thisName.orElse(top ? "this" : "_");
      ck(top && !n.equals("this")); if (!n.equals("_")){ names = names.add(list(n), list()); }
      var ms= splitBy(p -> p.splitOn(1, SemiColon), p -> p.parseMethod(top));
      var ns= flat(ms, m -> m.sig.flatMap(s -> s.m.map(nn -> new RCMName(s.rc, nn.withArity(m.arity())))).stream()); ck(dup(ns));
      ck(any(ns, nn -> nn.rc.isEmpty() && any(ns, o -> o.name.equals(nn.name) && o.rc.isPresent())));
      ck(dup(ms.stream().filter(m -> m.sig.flatMap(PSig::m).isEmpty()).map(PM::arity).toList())); return new PE.Lit(thisName, ms); }
    Stream<String> xsOf(Optional<XPat> xp){ return xp.stream().flatMap(XPat::parameterNames).filter(x -> !x.equals("_")); }
    void checkNewXs(List<String> xs){ ck(dup(xs) || any(xs, names.xs::contains)); }
    PM parseMethodWithSig(PSig sig){ var xs= flat(sig.ps, p -> xsOf(p.xp)); checkNewXs(xs);
      names = names.add(xs, bsXs(sig.bs)); var m= new PM(of(sig), of(parseAll(Parser::parseE)));
      var hasPats= sig.ps.stream().flatMap(p -> p.xp.stream()).anyMatch(XPat.Destruct.class::isInstance);
      ck(hasPats && xs.size() + (m.hasImplicit ? 1 : 0) > 32); return m; }
    static List<String> bsXs(Optional<List<B>> bs){ return B.xs(bs.orElse(list())); } PM parseMethod(boolean top){
      var m= parseFront(p -> p.splitOn(1, Arrow), Parser::parseSig).map(this::parseMethodWithSig); if (m.isPresent()){ return m.get(); }
      var hasSig= peek(DotName, Op) || peek(RCap) && peek(1, DotName, Op); if (!hasSig){ return new PM(empty(), of(parseAll(Parser::parseE))); }
      var sig= parseSig(); ck(!top); return new PM(of(sig), empty()); } PSig parseSig(){
      var rc= parseOptRC(); ck(rc.stream().anyMatch(r -> r.isH() || r == iso));
      var m= parseIf(peek(DotName, Op), () -> new MName(expect(DotName, Op).content, 0)); var bs= parseIf(peek(_SquareGroup), () -> parseBs(true));
      names = names.add(list(), bsXs(bs));
      var ps= peek(_RoundGroup) ? parseGroupSep(Parser::parseParameter, commaSkip) : peek(Colon) ? List.<Parameter>of() : splitBy(commaSkip, Parser::parseParameter);
      var t= parseIf(fwdIf(peek(Colon)), this::parseT); ck(!end()); var xs= flat(ps, p -> xsOf(p.xp));
      ck(dup(xs)); return new PSig(rc, m, bs, ps, t); } Parameter parseParameter(){
      var x= parseIf(peek(LowercaseId, Underscore, _CurlyGroup), this::parseXPat);
      var p= new Parameter(x, x.isPresent() ? parseIf(fwdIf(peek(Colon)), this::parseT) : of(parseT())); ck(!end()); return p; }
    List<B> parseBs(boolean mustNew){ var res= parseGroupSep(p -> p.parseB(mustNew), Parser::onCommaB); ck(dup(B.xs(res))); return res; } B parseB(boolean mustNew){
      var x= parseTX(mustNew).name; if (end()){ return new B(x, EnumSet.of(imm)); } expect(Colon); ck(end()); if (!peek(Op)){
        var rcs= splitBy(commaSkip, Parser::parseRC); ck(dup(rcs)); return new B(x, EnumSet.copyOf(rcs)); }
      return switch (expect(Op).content){ case "**" -> new B(x, allRC); case "*" -> new B(x, EnumSet.of(imm, mut, read));
        default -> throw new Fail(); }; } Declaration parseDeclaration(boolean top){ var c= parseTName(); ck(!isKind(c.s, _XId));
      var bs= peek(_SquareGroup) ? parseBs(top) : List.<B>of(); var Xs= B.xs(bs); var outer= names; var owner= top ? new Owner() : names.owner;
      names = new Names(names.xs, list(), push(names.hiddenXs, names.Xs), owner).add(list(), Xs); c = c.withArity(Xs.size()); owner.decs.add(c); expect(Colon);
      var cs= parseFront(p -> p.splitOn(2, _CurlyGroup), p -> p.splitBy(commaSkip, Parser::parseC)).orElseThrow(Fail::new); ck(dup(cs));
      var l= parseGroup(p -> p.parseLiteral(top)); names = outer; return new Declaration(c, bs, cs, l, owner); } FileFull parseFileFull(){ expect(_SOF);
      expectLast(_EOF); var maps= new ArrayList<String>(); var uses= new ArrayList<FileFull.Use>(); Function<Parser,Object> header= p -> {
        if (!p.peek(LowercaseId)){ return ""; } p.expectLast(SemiColon); return p.splitBy(q -> q.splitOn(1, SemiColon), q -> q.parseHeaderElement(maps, uses));
      }; if (parseFront(Parser::headEnd, header).isEmpty()){ parseAll(header); }
      var ds= splitBy(p -> p.splitOn(0, _CurlyGroup), p -> p.parseDeclaration(true)); return new FileFull(maps, uses, ds); }
    Token expectValidate(TK kind, TK validation){ ck(!peekIs(validation)); return expect(kind); } boolean peekIs(TK validation){ return peekIf(t -> isKind(t.content, validation)); }
    Object parseHeaderElement(ArrayList<String> maps, ArrayList<FileFull.Use> uses){ if (fwdIf(peekIs(_map))){
        var in= expectValidate(LowercaseId, _pkgName).content; expectValidate(LowercaseId, _as); expectValidate(LowercaseId, _pkgName);
        expectValidate(LowercaseId, _in); var key= in+" "+expectValidate(LowercaseId, _pkgName).content; ck(maps.contains(key)); maps.add(key); } else{
        ck(!fwdIf(peekIs(_use))); var t1= parseTName(); expectValidate(LowercaseId, _as);
        var t2= expectValidate(UppercaseId, _XId).content; ck(any(uses, u -> u.in.equals(t1) || u.out.equals(t2)));
        uses.add(new FileFull.Use(t1, t2)); } ck(!end()); return null; }
    <R> Optional<R> parseIf(boolean cond, Supplier<R> s){ return cond ? of(s.get()) : empty(); } int onCommaExp(){ var inColon= false; while (!end()){
        var t= expect(); if (t.is(Comma) && !inColon){ return 1; } if (!t.is(_SquareGroup, Comma, UppercaseId)){ inColon = false; }
        if (t.is(Colon)){ inColon = true; } } return 0; } int onCommaB(){ while (!end()){ if (expect().is(Comma) && !peek(RCap)){ return 1; } } return 0; }
    int headEnd(){ while (!(end() || isDec())){ expect(); } return 0; } static final ToIntFunction<Parser> commaSkip= p -> p.splitOn(1, Comma); }
  record Pkg(String name, Map<String,String> map, List<Declaration> decs, Set<TName> decNames){}
  record Scope(HashSet<String> used, HashMap<String,Integer> seq){ Scope(){ this(new HashSet<>(), new HashMap<>()); } }
  record Owner(Scope gen, Scope vars, ArrayList<TName> decs){ Owner(){ this(new Scope(), new Scope(), new ArrayList<>()); } }
  record Fresh(Scope top, HashSet<String> allGenericNames, HashMap<TName,Owner> owners, String pkgName){
    Fresh(Pkg p){ this(new Scope(), new HashSet<>(), new HashMap<>(), p.name);
      top.used.addAll(map(p.decNames, TName::simpleName)); top.used.addAll(p.map.keySet());
      for (var d : p.decs){ allGenericNames.addAll(d.owner.gen.used); owners.put(d.name.withPkgName(pkgName), d.owner); } }
    TName freshTopType(TName hint, int arity){
      var res= new TName(pkgName+"."+freshCandidate(hint.simpleName(), "ABCDEFGHJKMNPQRSTUVWXYZ", top, list(allGenericNames)), arity); owners.put(res, owners.get(hint)); return res; }
    boolean isFreshGeneric(TName owner, String x, List<String> scope){ return !owners.get(owner).gen.used.contains(x) && !top.used.contains(x) && !scope.contains(x); }
    String freshGeneric(TName owner, String hint, List<String> siblings){
      var cand= freshCandidate(hint, "ABCDEFGHJKMNPQRSTUVWXYZ", owners.get(owner).gen, list(top.used, siblings)); allGenericNames.add(cand); return cand; }
    String freshVar(TName owner, String hint){ return freshCandidate(hint, "abcdefghjkmnpqrstuvwxyz", owners.get(owner).vars, list()); }
    static String freshCandidate(String hint, String alphabet, Scope s, List<Collection<String>> extraChecks){
      var base= hint.replaceAll("[^A-Za-z0-9]", "").replaceFirst("(?<=.{4}).*", ""); for (int n= s.seq.getOrDefault(base, 1);; n += 1){
        var sb= new StringBuilder(); for (int k= n; k > 0; k = (k-1) / alphabet.length()){ sb.append(alphabet.charAt((k-1) % alphabet.length())); }
        var cand= "_"+sb.reverse()+base; if (s.used.contains(cand) || any(extraChecks, e -> e.contains(cand))){ continue; }
        s.used.add(cand); s.seq.put(base, n+1); return cand; } } }
  static final TName baseStr= new TName("base.Str", 0), baseNat= new TName("base.Nat", 0), baseInt= new TName("base.Int", 0), baseFloat= new TName("base.Float", 0),
    widen= new TName("base.WidenTo", 1), sealed= new TName("base.Sealed", 0), captureFree= new TName("base.CaptureFree", 0), baseId= new TName("base.BaseId", 2),
    baseContainer= new TName("base.BaseContainer", 1), inferUnknown= new TName("base.InferUnknown", 0);
  static final List<TName> inferErrs= list(new TName("base.InferErr", 2), new TName("base.InferErr", 3), new TName("base.InferErr", 4));
  static final EnumSet<RC> isoImm= EnumSet.of(iso, imm), noHyg= EnumSet.of(iso, imm, mut, read), allRC= EnumSet.allOf(RC.class);
  static boolean has(List<C> cs, TName magic){ return any(cs, c -> c.name.equals(magic)); }
  static boolean isPrimitiveLiteral(String name){ return "+-1234567890\"`".contains(name.substring(0, 1)); }
  static Literal from(TName n, Function<TName,Literal> map, Map<TName,Literal> other){ var res= map.apply(n); if (res == null){ res = other.get(n); }
    if (res != null || !n.pkgName().equals("base") || !isPrimitiveLiteral(n.simpleName())){ return res; } var s= n.simpleName();
    var lit= s.startsWith("`") || s.startsWith("\"") ? baseStr : isKind(s, UnsignedInt) ? baseNat : isKind(s, SignedInt) ? baseInt : baseFloat;
    var sup= from(lit, map, other); var ms= map(sup.ms, m -> m.withSig(new ISig(m.sig.rc, m.sig.m, m.sig.bs, m.sig.ts, m.sig.ret, of(n), false, m.sig.idx)));
    return new Literal(of(imm), n, list(), push(new C(lit, list()), sup.cs), "this", ms, true); }
  static boolean inRange(String raw, BigInteger min, BigInteger max){ var b= new BigInteger(raw.replace("_", "")); return b.compareTo(min) >= 0 && b.compareTo(max) <= 0; }
  static boolean floatOk(String raw){ var soft= raw.endsWith("soft"); var ns= raw.replace("soft", "").replace("_", ""); var d= Double.parseDouble(ns);
    return Double.isFinite(d) && (soft || (d == 0 ? new BigDecimal(ns.replaceAll("[eE].*", "")) : new BigDecimal(ns).subtract(new BigDecimal(d))).signum() == 0); }
  public sealed interface IT{ default boolean isTV(){ return true; }
    default long badness(){ return 0; } default Optional<RC> explicitRC(){ return empty(); } default int depth(){ return 1; }
    record X(String name) implements IT{} record RCX(RC rc, X x) implements IT{ @Override public Optional<RC> explicitRC(){ return of(rc); } }
    record ReadImmX(X x) implements IT{} record C(TName name, List<IT> ts, int depth){
      C(TName name, List<IT> ts){ this(name, ts, 1+ts.stream().mapToInt(IT::depth).max().orElse(1)); } }
    record RCC(Optional<RC> rc, C c) implements IT{ public RCC{ if (c.depth > 100){ throw new Fail(); } } RCC withTs(List<IT> ts){ return withRCTs(rc, ts); }
      RCC withRCTs(Optional<RC> rc, List<IT> ts){ var c1= new C(c.name, ts); return c1.depth > 100 ? this : new RCC(rc, c1); }
      @Override public long badness(){ return c.ts.stream().mapToLong(IT::badness).sum(); }
      @Override public boolean isTV(){ return all(c.ts, IT::isTV); } @Override public int depth(){ return c.depth; }
      @Override public Optional<RC> explicitRC(){ return rc; } } enum U implements IT{ Instance;
      @Override public boolean isTV(){ return false; } @Override public long badness(){ return 1; } } default IT withRC(RC rc){ return switch (this){
      case RCC(_, var c) -> new RCC(of(rc), c); case RCX(_, var x) -> new RCX(rc, x); case X x -> new RCX(rc, x);
      case ReadImmX(var x) -> new RCX(rc, x); case U _ -> this; };} default Stream<String> ftv(){ return switch (this){ case X(var name) -> Stream.of(name);
      case RCX(_, var x) -> x.ftv(); case ReadImmX(var x) -> x.ftv(); case RCC(_, var c) -> c.ts.stream().flatMap(IT::ftv); case U _ -> Stream.of(); };}
    default IT readImm(){ return switch (this){ case X x -> new ReadImmX(x); case ReadImmX _ -> this;
      case RCC(var rc, var c) -> new RCC(rc.map(RC::readImm), c); case RCX(var rc, var x) -> new RCX(rc.readImm(), x); case U _ -> this; };} }
  public sealed interface IE{ IT t(); IE withT(IT t); default Stream<IE> children(){ return switch (this){
      case X _, Type _ -> Stream.of(); case Literal l -> l.ms.stream().flatMap(m -> m.e.stream()); case Call c -> Stream.concat(Stream.of(c.e), c.es.stream()); };}
    record X(String name, IT t) implements IE{ X(String name){ this(name, U.Instance); }
      @Override public IE withT(IT t){ return t.equals(this.t) ? this : new X(name, t); } }
    record Type(RCC type, IT t) implements IE{ Type(RCC type){ this(type, U.Instance); }
      @Override public IE withT(IT t){ return t.equals(this.t) ? this : new Type(type, t); } }
    record Call(IE e, MName name, Optional<RC> rc, List<IT> targs, List<IE> es, IT t, boolean written) implements IE{
      Call(IE e, MName name, Optional<RC> rc, List<IT> targs, List<IE> es, boolean written){ this(e, name, rc, targs, es, U.Instance, written); }
      Call withEEs(IE e, List<IE> es){ return e == this.e && es == this.es ? this : new Call(e, name, rc, targs, es, t, written); }
      @Override public Call withT(IT t){ return t.equals(this.t) ? this : new Call(e, name, rc, targs, es, t, written); } } }
  public record Literal(Optional<RC> rc, TName name, List<B> bs, List<C> cs, String thisName, List<IM> ms, IT t, boolean infName, boolean infHead) implements IE{
    Literal(Optional<RC> rc, TName name, List<B> bs, List<C> cs, String thisName, List<IM> ms, boolean infName){
      this(rc, name, bs, cs, thisName, ms, U.Instance, infName, false); }
    @Override public Literal withT(IT t){ return t.equals(this.t) ? this : new Literal(rc, name, bs, cs, thisName, ms, t, infName, infHead); }
    Literal withMsT(List<IM> ms, IT t){ if (infHead && ms == this.ms && t.equals(this.t)){ return this; }
      return new Literal(rc, name, bs, cs, thisName, ms, t, infName, true); } Literal withCsMs(List<C> cs, List<IM> ms, boolean setInfHead){
      if (infHead == setInfHead && cs.equals(this.cs) && ms == this.ms){ return this; }
      return new Literal(rc, name, bs, cs, thisName, ms, t, infName, setInfHead); }
    RCC self(Optional<RC> rc){ return new RCC(rc, new C(name, toXs(B.xs(bs)))); }
    Literal withRC(RC rc){ return new Literal(of(rc), name, bs, cs, thisName, ms, infName); } }
  public record IM(ISig sig, List<String> xs, Optional<IE> e){ IM(ISig sig){ this(sig, Collections.nCopies(sig.ts.size(), "_"), empty()); }
    IM withSig(ISig sig){ return sig.equals(this.sig) ? this : new IM(sig, xs, e); } }
  public record ISig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<IT> ts, IT ret, Optional<TName> origin, boolean abs, int idx){
    ISig(RC rc, MName m, List<B> bs, List<IT> ts, IT ret, TName origin, boolean abs, int idx){
      this(of(rc), of(m), of(bs), ts, ret, of(origin), abs, idx); }
    ISig withTsT(List<IT> ts, IT ret){ return new ISig(rc, m, bs, ts, ret, origin, abs, idx); }
    ISig withOrigin(TName origin){ return new ISig(rc, m, bs, ts, ret, of(origin), abs, idx); }
    ISig subst(List<B> bs, List<String> xs, List<IT> ts){
      return new ISig(rc, m, of(bs), renameIT(this.ts, xs, ts), rename(ret, xs, ts), origin, abs, idx); } }
  static final class IGamma{
    record Frame(RC rc, List<B> bs, HashMap<String,IT> vars){}
    final ArrayList<Frame> fs= new ArrayList<>(list(new Frame(null, list(), new HashMap<>())));
    int at(String x){ return IntStream.range(0, fs.size()).filter(i -> fs.get(i).vars.containsKey(x)).findFirst().orElse(-1); }
    IT get(String x){ var i= at(x); return i == -1 ? null : fs.get(i).vars.get(x); } IT getWithRC(String x){ var i= at(x); var t= get(x);
      for (var s= i + 1; s < fs.size(); s += 1){ t = adapt(t, fs.get(s).rc, fs.get(s).bs); } return t; } boolean notFunnelledInto(String x){
      var fxs= get(x).ftv().toList(); return IntStream.range(at(x) + 1, fs.size()).anyMatch(s -> !B.xs(fs.get(s).bs).containsAll(fxs)); }
    static IT adapt(IT t, RC rc, List<B> bs){ var x= t instanceof X(var n) ? n : t instanceof ReadImmX(X(var n)) ? n : null; if (x != null){
        var xRcs= B.get(bs, x).rcs; if (rc == imm || isoImm.containsAll(xRcs)){ return t.withRC(imm); }
        if (any(xRcs, RC::isH)){ return t; } return rc == read || xRcs.contains(iso) ? t.readImm() : t; } var trc= t.explicitRC();
      if (rc == imm || trc.equals(of(iso))){ return t.withRC(imm); } if (rc == mut){ return t; }
      if (trc.equals(of(mutH))){ return t.withRC(readH); } return trc.equals(of(mut)) ? t.withRC(read) : t; }
    void declare(String x, IT t){ if (!x.equals("_")){ fs.getLast().vars.put(x, t); } }
    Object snap(){ var m= new HashMap<String,IT>(); fs.forEach(f -> m.putAll(f.vars)); return m; } }
  static C normC(C c){ return new C(c.name, map(c.ts, Frontend::norm)); } static IT norm(IT t){ return switch (t){
    case RCC(var rc, var c) -> new RCC(of(rc.orElse(imm)), normC(c)); case U _ -> inferUnknownT; default -> t; };}
  static final RCC inferUnknownT= new RCC(of(imm), new C(inferUnknown, list()));  static boolean isInfer(IT t){ return t instanceof RCC(_, var c) && (c.name.equals(inferUnknown) || inferErrs.contains(c.name)); }
  static IT rename(IT t, List<String> xs, List<IT> ts){ return switch (t){ case X x -> xs.contains(x.name) ? ts.get(xs.indexOf(x.name)) : x;
      case RCX(var rc, var x) -> { var r= rename(x, xs, ts); yield isInfer(r) ? r : r.withRC(rc); } case RCC rcc -> rcc.withTs(renameIT(rcc.c.ts, xs, ts));
      case ReadImmX(var x) -> { var r= rename(x, xs, ts); yield isInfer(r) ? r : r.readImm(); } case U _ -> t; }; }
  static List<IT> renameIT(List<IT> tsi, List<String> xs, List<IT> ts){ return map(tsi, ti -> rename(ti, xs, ts)); }
  static List<IT> toXs(List<String> xs){ return xs.stream().<IT>map(X::new).toList(); }
  static List<IT> qMarks(int n){ return Collections.nCopies(n, U.Instance); }
  record MSigL(RC rc, List<String> xs, List<B> clsBs, List<IT> clsArgs, List<B> methBs, List<IT> ps0, IT ret0){
    MSigL withClsArgs(List<IT> clsArgs){ return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0); }
    IT inst(IT t, List<IT> targs){ return rename(t, xs, push(clsArgs, fixTargs(targs, methBs.size()))); }
    static List<IT> fixTargs(List<IT> targs, int n){ return targs.size() > n ? targs.subList(0, n) : push(targs, qMarks(n-targs.size())); } }
  static Stream<String> ftvE(IGamma g, IE e){ return switch (e){
    case IE.X(var name, var t) -> Stream.concat(t.ftv(), Stream.ofNullable(g.get(name)).flatMap(IT::ftv));
    case Literal l -> cat(l.bs.stream().map(B::x), ftvCs(l.cs), ftvMs(g, l.ms));
    case Call(var ei, _, _, var targs, var es, _, _) -> cat(ftvE(g, ei), targs.stream().flatMap(IT::ftv), es.stream().flatMap(x -> ftvE(g, x)));
    case Type(var t, _) -> t.ftv(); };}
  static Stream<String> ftvCs(List<C> cs){ return cs.stream().flatMap(c -> c.ts.stream().flatMap(IT::ftv)); }
  static Stream<String> ftvMs(IGamma g, List<IM> ms){ return ms.stream().flatMap(m -> { var domBs= B.xs(m.sig.bs.orElse(list()));
      return cat(m.sig.ts.stream().flatMap(IT::ftv), m.sig.ret.ftv(), m.e.stream().flatMap(ei -> ftvE(g, ei))).filter(x -> !domBs.contains(x));
    }); } static IE copy(Fresh fresh, IE e){ return switch (e){ case IE.X(var name, var t) -> new IE.X(name, t);
    case Type(var type, var t) -> new Type(type, t);
    case Call c -> new Call(copy(fresh, c.e), c.name, c.rc, c.targs, map(c.es, x -> copy(fresh, x)), c.t, c.written);
    case Literal l -> { ck(!l.infName); var newName= fresh.freshTopType(l.name, l.name.arity);
      yield new Literal(l.rc, newName, l.bs, l.cs, l.thisName, map(l.ms, m -> copyM(fresh, m, l.name, newName)), l.t, true, l.infHead);
    } };} static IM copyM(Fresh fresh, IM m, TName oldName, TName newName){
    var sig= m.sig.origin.equals(of(oldName)) ? m.sig.withOrigin(newName) : m.sig;
    return new IM(sig, m.xs, m.e.map(ei -> copy(fresh, ei))); } static List<Literal> toInference(Methods meths){ var v= new Visitor(meths);
    for (var di : meths.p.decs){ v.currentTop = v.f(di.name); v.addDeclaration(v.currentTop, mut, di, true); } return v.decs; } record XE(String x, PE e){}
  static final class Visitor{ final Methods meths; TName currentTop; final ArrayList<String> implicits= new ArrayList<>(); final ArrayList<Literal> decs= new ArrayList<>();
    Visitor(Methods meths){ this.meths= meths; } TName f(TName tn){ var p= meths.p; var pN= tn.pkgName(); if (pN.isEmpty() && isPrimitiveLiteral(tn.s)){ return tn.withPkgName("base"); }
      var full= new TName(pN.isEmpty() ? p.map.getOrDefault(tn.s, p.name+"."+tn.s) : p.map.getOrDefault(pN, pN)+"."+tn.simpleName(), tn.arity);
      ck(!(full.pkgName().equals(p.name) ? p.decNames.contains(new TName(full.simpleName(), full.arity)) : meths.other.containsKey(full))); return full; }
    IT visitT(IT t){ return t instanceof RCC(var rc, var c) ? new RCC(rc, visitC(c)) : t; } IE visitE(PE e){ return switch (e){
        case PE.X x -> new IE.X(x.name); case PE.Implicit _ -> new IE.X(implicits.getLast());
        case PE.TypedLiteral t -> t.l.isEmpty() ? new Type(new RCC(of(t.rc), visitC(t.c))) : liftLiteral(of(t.rc), list(visitC(t.c)), t.l.get());
        case PE.DeclarationLiteral c -> { var name= f(c.dec.name); meths.fresh.owners.put(name, meths.fresh.owners.get(currentTop));
          yield addDeclaration(name, c.rc.orElse(imm), c.dec, false); } case PE.Lit l -> liftLiteral(empty(), list(), l); case PE.Call c0 -> {
          var c= c0.pat.isPresent() ? desugarCPat(c0) : c0; var recv= visitE(c.e); var es= map(c.es, this::visitE);
          var sq= c.targs.orElse(new PE.CallSquare(empty(), list()));
          yield new Call(recv, c.name, sq.rc, map(sq.ts, this::visitT), es, c.targs.isPresent()); } }; } C visitC(C c){ var s= c.name.s;
      var bad= isPrimitiveLiteral(s) && (isKind(s, UnsignedInt) && !inRange(s, BigInteger.ZERO, new BigInteger(Long.toUnsignedString(-1L)))
        || isKind(s, SignedInt) && !inRange(s, BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE))
        || isKind(s, SignedFloat, UnSignedFloat) && !floatOk(s)); ck(bad); return new C(f(c.name), map(c.ts, this::visitT)); }
    String parameterToName(Parameter p, boolean hasPat){ if (p.xp.isEmpty()){ return "_"; } return switch (p.xp.get()){
        case XPat.Name(var x) -> hasPat && !x.equals("_") ? meths.fresh.freshVar(currentTop, x) : x;
        case XPat.Destruct _ -> meths.fresh.freshVar(currentTop, "div"); }; }
    List<IM> visitMs(List<PM> ms){ return IntStream.range(0, ms.size()).mapToObj(i -> visitM(ms.get(i), i)).toList(); }
    ISig visitMSig(PM mm, int idx){ IT u= U.Instance; var s= mm.sig.orElse(new PSig(empty(), empty(), empty(), list(), empty()));
      var ts= map(s.ps, p -> p.t.map(this::visitT).orElse(u)); if (mm.hasImplicit){ ts = push(ts, u); }
      return new ISig(s.rc, s.m.map(mi -> mi.withArity(mm.arity())), s.bs, ts, s.t.map(this::visitT).orElse(u), empty(), mm.body.isEmpty(), idx); } IM visitM(PM m, int idx){ var sig= visitMSig(m, idx);
      if (m.body.isEmpty()){ return new IM(sig); } var body= m.body.get(); var original= m.sig.map(s -> s.ps).orElse(list());
      var hasPat= any(original, p -> p.xp.stream().anyMatch(XPat.Destruct.class::isInstance));
      var ps= map(original, p -> parameterToName(p, hasPat));
      var xpats= flat(zip(ps, original, (x,p) -> p.xp.stream().flatMap(xp -> xpat(xp, x))), s -> s); if (m.hasImplicit){
        var p= meths.fresh.freshVar(currentTop, "impl"); var inner= hasPat ? meths.fresh.freshVar(currentTop, "impl") : p; ps = push(ps, p);
        if (hasPat){ xpats = push(xpats, new XE(inner, new PE.X(p))); } implicits.add(inner); } if (hasPat){
        var pps= map(xpats, xe -> new Parameter(of(new XPat.Name(xe.x)), empty()));
        var fl= new PE.Lit(empty(), list(new PM(of(new PSig(empty(), empty(), empty(), pps, empty())), of(body), false)));
        body = new PE.Call(new PE.TypedLiteral(imm, new C(new TName("base.Destruct", 0), list()), empty()), new MName("#", xpats.size()+1), empty(), empty(), push(map(xpats, XE::e), fl));
      } var e= visitE(body); if (m.hasImplicit){ implicits.removeLast(); } return new IM(sig, ps, of(e)); }
    Stream<XE> xpat(XPat xp, String lowered){ return switch (xp){ case XPat.Destruct d -> zip(d.extract, d.parameterNames().toList(), (e,x) -> {
        PE res= new PE.X(lowered); for (var m : e){ res = new PE.Call(res, new MName(m.s, 0), empty(), empty(), list()); } return new XE(x, res); }).stream();
      case XPat.Name(var x) -> x.equals(lowered) ? Stream.of() : Stream.of(new XE(x, new PE.X(lowered))); };}
    Literal liftLiteral(Optional<RC> rc, List<C> impl, PE.Lit l){ var ms= visitMs(l.ms);
      return new Literal(rc, meths.fresh.freshTopType(currentTop, 0), list(), impl, l.thisName.orElse("_"), ms, true); }
    Literal addDeclaration(TName name, RC rc, Declaration d, boolean top){ var thisName= d.l.thisName.orElse(top ? "this" : "_");
      var bs= d.bs; var cs= map(d.cs, this::visitC);
      ck(duplicatedSupertypes(bs, map(cs, Frontend::normC)));
      var l= new Literal(of(rc), name, bs, cs, thisName, visitMs(d.l.ms), false); decs.add(l); return l;
    } PE.Call desugarCPat(PE.Call c){ var fresh= new PE.X(meths.fresh.freshVar(currentTop, "eqS")); var res= replaceAtom(c.es.get(1), fresh);
      var sig= new PSig(empty(), empty(), empty(), list(new Parameter(c.pat, empty()), new Parameter(of(new XPat.Name(fresh.name)), empty())), empty());
      var par2= new PE.Lit(empty(), list(new PM(of(sig), of(res), false)));
      return new PE.Call(c.e, c.name, c.targs, empty(), list(c.es.getFirst(), par2)); } PE replaceAtom(PE par, PE atom){
      if (!(par instanceof PE.Call c)){ return atom; } return new PE.Call(replaceAtom(c.e, atom), c.name, c.targs, c.pat, c.es); } }
  static boolean duplicatedSupertypes(List<B> bs, List<C> cs){ var ts= map(cs, c -> new RCC(of(imm), c));
    return IntStream.range(0, ts.size()).anyMatch(j -> IntStream.range(0, j).anyMatch(i -> TypeSystem.isSameShapeSubtype(bs, ts.get(i), ts.get(j)) && TypeSystem.isSameShapeSubtype(bs, ts.get(j), ts.get(i))));
  } static final class Methods{
    final Pkg p; final Map<TName,Literal> other; final Fresh fresh; final HashMap<TName,Literal> cache= new HashMap<>();
    final IdentityHashMap<IE,Object> memo= new IdentityHashMap<>();
    Methods(Pkg p, Map<TName,Literal> other){ this.p= p; this.other= other; fresh= new Fresh(p); }
    List<Literal> headers(List<Literal> iDecs){ var rem= new LinkedHashMap<TName,Literal>();
      iDecs.forEach(d -> rem.put(d.name, d)); var acc= new ArrayList<Literal>(); while (!rem.isEmpty()){
        var layer= filter(rem.values(), d -> !any(d.cs, c -> c.name.pkgName().equals(p.name) && rem.containsKey(c.name)));
        ck(layer.isEmpty()); for (var d : layer){ rem.remove(d.name); var e= expandDeclaration(d, false); if (d.thisName.equals("this")){ acc.add(e); }
          register(e); } } return acc; } List<C> fetchCs(C c){ var d= from(c.name); if (d == null){ return list(); }
      return d.cs.stream().map(ci -> new C(ci.name, renameIT(ci.ts, B.xs(d.bs), c.ts))).distinct().toList(); }
    List<ISig> fetchSigs(Literal child, C c, Literal d, List<String> scope){ return map(d.ms, m -> alphaSig(m, d, c, child, scope)); }
    ISig alphaSig(IM m, Literal d, C c, Literal child, List<String> scope){ var s= m.sig; var fullXs= new ArrayList<>(B.xs(d.bs));
      var fullTs= new ArrayList<>(c.ts); var newBs= new ArrayList<B>(); for (var b : s.bs.get()){ var x= b.x;
        if (fresh.isFreshGeneric(child.name, x, scope)){ newBs.add(b); continue; } fullXs.add(x);
        var newX= new X(fresh.freshGeneric(child.name, x, push(B.xs(s.bs.get()), scope))); fullTs.add(newX); newBs.add(new B(newX.name, b.rcs)); }
      return s.subst(newBs, fullXs, fullTs); }
    Literal from(TName name){ return Frontend.from(name, cache::get, other); } Literal expandDeclaration(Literal d, boolean setInfHead){
      var implied= flat(d.cs, c -> fetchCs(c).stream());
      var allCs= ToCore.distinctTypes(d.bs, push(d.cs, implied.stream().sorted(Comparator.comparing(Print::of)).toList()));
      var allSig= flat(filter(d.cs, c -> !implied.contains(c)), c -> fetchSigs(d, c, from(c.name), list()).stream());
      var res= d.withCsMs(allCs, pair(inferMNames(d.ms, new ArrayList<>(allSig)), new ArrayList<>(allSig), d), setInfHead);
      checkMagicSupertypes(res, allCs); return res; } Literal expandLiteral(Literal d, C c, List<B> scope){ var dd= from(c.name);
      List<ISig> allSig= dd == null ? list() : fetchSigs(d, c, dd, B.xs(scope));
      return d.withCsMs(push(c, fetchCs(c)), pair(inferMNames(d.ms, new ArrayList<>(allSig)), new ArrayList<>(allSig), d), true); }
    void checkMagicSupertypes(Literal d, List<C> allCs){ ck(allCs.stream().filter(c -> c.name.equals(widen)).count() > 1);
      if (any(allCs, c -> c.name.equals(baseId))){ var ms= d.ms;
        ck(ms.size() != 1 || !ms.getFirst().sig.m.get().equals(new MName("#", 1))); var s= ms.getFirst().sig;
        ck(!(ms.getFirst().e.isPresent() || s.abs || has(from(s.origin.get()).cs, baseId))); }
      if (!any(allCs, c -> c.name.equals(sealed))){ return; }
      ck(any(allCs, c -> !c.name.pkgName().equals(d.name.pkgName()) && has(from(c.name).cs, sealed))); } void register(Literal d){
      var ms= map(d.ms, m -> m.withSig(ToCore.sig(m.sig, m.sig)));
      cache.put(d.name, new Literal(of(d.rc.orElse(imm)), d.name, d.bs, map(d.cs, Frontend::normC), d.thisName, ms, d.infName)); }
    List<IM> inferMNames(List<IM> ms, ArrayList<ISig> ss){ ss.removeIf(s -> any(ms, m -> m.sig.m.equals(s.m)));
      var named= filter(ms, m -> m.sig.m.isPresent());
      return named.size() == ms.size() ? ms : push(named, ms.stream().filter(m -> m.sig.m.isEmpty()).map(m -> nameFromSigs(m, ss)).toList()); } IM nameFromSigs(IM m, ArrayList<ISig> ss){
      var arity= m.sig.ts.size(); for (var abs : list(true, false)){
        var match= filter(ss, s -> s.m.get().arity == arity && (s.abs || !abs)); ss.removeAll(match);
        var count= match.stream().map(s -> s.m.get()).distinct().count(); ck(count > 1); if (count == 1){ var s= m.sig;
          return m.withSig(new ISig(s.rc, match.getFirst().m, s.bs, s.ts, s.ret, s.origin, s.abs, s.idx)); } } throw new Fail(); }
    List<IM> pair(List<IM> ms, ArrayList<ISig> ss, Literal origin){ var res= new ArrayList<IM>(); for (var m : ms){
        var name= m.sig.m.get(); var rc= m.sig.rc;
        var taken= filter(ss, s -> s.m.get().equals(name) && (rc.isEmpty() || rc.equals(s.rc))); ss.removeAll(taken);
        var match= group(taken, s -> s.rc.get());
        if (rc.isEmpty() && match.size() > 1 && noH(origin.rc.or(origin.t::explicitRC).orElse(imm)).isReadOrImm()){
          var dead= match.remove(mut); if (dead != null){ ss.addAll(dead); } } var first= true;
        for (var matches : match.isEmpty() ? list(List.<ISig>of()) : match.values()){
          var mi= first ? m : copyM(fresh, m, origin.name, origin.name); first = false; res.add(pair(matches, of(mi), origin)); } }
      group(ss, s -> new RCMName(s.rc, s.m.get())).values().forEach(v -> res.add(pair(v, empty(), origin)));
      return res.size() == ms.size() ? same(ms, res) : res; }
    IM pair(List<ISig> ss, Optional<IM> om, Literal origin){ if (om.isEmpty() && ss.size() == 1){ return new IM(ss.getFirst()); }
      var s= om.map(IM::sig).orElseGet(() -> new ISig(empty(), empty(), empty(), qMarks(ss.getFirst().m.get().arity), U.Instance, empty(), false, 0));
      if (ss.isEmpty()){ ck(any(s.ts, t -> t instanceof U) || s.ret instanceof U);
        return om.get().withSig(new ISig(s.rc.orElse(imm), s.m.get(), s.bs.orElse(list()), s.ts, s.ret, origin.name, om.get().e.isEmpty(), s.idx)); }
      var bs= s.bs.orElse(ss.getFirst().bs.get()); var rcss= ss.stream().map(e -> map(e.bs.get(), B::rcs)).distinct().toList();
      ck(rcss.size() != 1 || !rcss.getFirst().equals(map(bs, B::rcs)));
      var ssAligned= alignSigs(ss, bs); var first= ssAligned.getFirst();
      var ts= IntStream.range(0, s.ts.size()).mapToObj(i -> s.ts.get(i) instanceof U ? agreement(origin, ssAligned, e -> e.ts.get(i)) : s.ts.get(i)).toList();
      var res= s.ret instanceof U ? agreement(origin, ssAligned, ISig::ret) : s.ret;
      var impl= om.isPresent() ? List.<TName>of() : ssAligned.stream().filter(e -> !e.abs && !overridden(e, origin)).map(e -> e.origin.get()).distinct().toList(); ck(impl.size() > 1);
      var sig= new ISig(s.rc.orElse(first.rc.get()), first.m.get(), bs, ts, res, impl.size() == 1 ? impl.getFirst() : origin.name, om.map(mi -> mi.e.isEmpty()).orElse(impl.isEmpty()), s.idx);
      return om.map(mi -> mi.withSig(sig)).orElseGet(() -> new IM(sig)); } boolean overridden(ISig s, Literal lit){ var sup= s.origin.get(); return lit.cs.stream()
        .flatMap(c -> Stream.concat(Stream.of(c.name), from(c.name).cs.stream().map(C::name))) .anyMatch(t -> { var d= from(t);
          return !t.equals(sup) && has(d.cs, sup) && d.ms.stream().map(IM::sig).anyMatch(o -> o.origin.get().equals(d.name) && o.m.equals(s.m) && o.rc.equals(s.rc));
        }); } IT agreement(Literal lit, List<ISig> ss, Function<ISig,IT> f){ var res= ss.stream().map(f).distinct().toList();
      var bs= push(lit.bs, ss.getFirst().bs.get()); var first= Frontend.norm(res.getFirst());
      ck(!all(res, t -> TypeSystem.eqModXRC(bs, first, Frontend.norm(t)))); return res.getFirst(); }
    List<ISig> alignSigs(List<ISig> ss, List<B> bs){ return map(ss, s -> s.subst(bs, B.xs(s.bs.get()), toXs(B.xs(bs)))); }
    List<Literal> steps(List<Literal> tops){
      return map(tops, l -> { var di= cache.get(l.name); return di.withCsMs(di.cs, zip(l.ms, di.ms, (m,mCore) -> stepDecM(di, mCore, m)), false); }); }
    IM stepDecM(Literal di, IM mCore, IM m){
      if (m.e.isEmpty()){ return mCore; } var e= m.e.get(); var xs= m.xs; var ei= meet(e, mCore.sig.ret); var g= new IGamma();
      for (int i= 0; i < xs.size(); i++){ g.declare(xs.get(i), mCore.sig.ts.get(i)); }
      g.declare(di.thisName, di.self(mCore.sig.rc)); var bs= push(di.bs, m.sig.bs.get());
      ei = nextStar(bs, g, ei); return new IM(mCore.sig, xs, of(new ToCore(bs).core(ei, e))); } IE meet(IE e, IT t){
      if (e instanceof Type tt){ return nextT(tt); } if (e instanceof Literal l && l.t.isTV()){ return e; } e = ascribe(e, t, false);
      return e.withT(meet(e.t(), t)); } IT leastBad(RCC a, RCC b){ var aSuper= isSuper(a.c.name, b.c.name);
      var bSuper= isSuper(b.c.name, a.c.name);
      var aBad= bSuper ? Math.max(adaptedSuperTs(a, b.c.name).getFirst().badness(), a.badness()) : a.badness();
      var bBad= aSuper ? Math.max(adaptedSuperTs(b, a.c.name).getFirst().badness(), b.badness()) : b.badness();
      if (aBad != bBad){ return aBad < bBad ? a : b; } if (aSuper){ return b; } if (bSuper){ return a; }
      if (a.depth() != b.depth()){ return a.depth() < b.depth() ? a : b; } return a.c.name.s.compareTo(b.c.name.s) < 0 ? a : b; }
    IT leastBad(IT a, IT b){ var ra= rank(a); var rb= rank(b); return ra != rb ? (ra > rb ? a : b) : Print.of(a).compareTo(Print.of(b)) < 0 ? a : b; }
    static int rank(IT t){ return t instanceof RCC ? 2 : t instanceof RCX ? 1 : 0; }
    IT meet(IT t1, IT t2){ if (t2 instanceof U || t1.equals(t2)){ return t1; } if (t1 instanceof U){ return t2; }
      if (t1 instanceof ReadImmX(var x1) && x1.equals(t2)){ return t1; } if (t2 instanceof ReadImmX(var x2) && x2.equals(t1)){ return t2; }
      if (t1 instanceof RCC x1 && t2 instanceof RCC x2){ if (!x1.c.name.equals(x2.c.name)){ return leastBad(x1, x2); }
        return x1.withRCTs(meetRcNoH(x1.rc, x2.rc), meet(x1.c.ts, x2.c.ts)); }
      if (!(t1 instanceof RCX x1 && t2 instanceof RCX(var rc2, var x2)) || !x1.x.equals(x2)){ return leastBad(t1, t2); }
      return x1.withRC(meetRcNoH(of(x1.rc), of(rc2)).get()); } static Optional<RC> meetRcNoH(Optional<RC> a, Optional<RC> b){
      if (a.isEmpty()){ return b; } if (b.isEmpty()){ return a; } var x= noH(a.get()); var y= noH(b.get());
      if (x == y || y == iso || y == read && x != iso){ return of(x); } if (x == iso || x == read){ return of(y); }
      return of(imm); } static RC noH(RC a){ return a == readH ? read : a == mutH ? mut : a; }
    List<IT> meet(List<IT> t1, List<IT> t2){ return zip(t1, t2, this::meet); }
    List<IT> meet(List<List<IT>> tss){ return tss.stream().reduce(this::meet).get(); } IE nextStar(List<B> bs, IGamma g, IE e){
      if (g.snap().equals(memo.get(e))){ return e; } while (true){ var s= g.snap(); var oe= next(bs, g, e);
        if (oe == e && s.equals(g.snap())){ memo.put(e, s); return e; } e = oe; } }
    List<IE> nextStar(List<B> bs, IGamma g, List<IE> es){ return same(es, map(es, ei -> nextStar(bs, g, ei))); }
    List<IE> meetWithTargs(List<IE> es, MSigL m, List<IT> targs){ return same(es, zip(es, m.ps0, (e,p) -> meet(e, m.inst(p, targs)))); }
    IE next(List<B> bs, IGamma g, IE e){ return switch (e){ case IE.X x -> { ck(g.notFunnelledInto(x.name));
          var t1= g.getWithRC(x.name); var t2= x.t; if (t1.equals(t2)){ yield x; } if (!(t2 instanceof U)){ updateG(g, x.name, t2); }
          yield x.withT(meet(t1, t2)); } case Literal l -> nextL(bs, g, l); case Call c when c.written || c.rc.isPresent() -> nextC(bs, g, c); case Call c -> {
          var ee= nextStar(bs, g, c.e); var es= nextStar(bs, g, c.es);
          if (!(ee.t() instanceof RCC rcc) || methodHeader(rcc, c.name, empty()).isEmpty()){ yield c.withEEs(ee, es); } var m= methodHeader(rcc, c.name, empty()).get();
          var ts= qMarks(m.methBs.size());
          yield new Call(ee, c.name, of(m.rc), ts, meetWithTargs(es, m, ts), false).withT(meet(c.t, m.inst(m.ret0, ts))); }
        case Type c -> nextT(c); }; } IT preferred(RCC type){ var d= from(type.c.name);
      var c= find(d.cs, ci -> ci.name.equals(widen)); if (c.isEmpty()){ return type; }
      var wid= rename(c.get().ts.getFirst(), B.xs(d.bs), type.c.ts); if (!(wid instanceof RCC(_, var widC))){ return type; }
      return new RCC(type.rc, widC); } Optional<IM> methodHeaderIM(RCC rcc, MName name, Optional<RC> favorite){
      var d= from(rcc.c.name); if (d == null){ return empty(); } var ms= filter(d.ms, m -> m.sig.m.get().equals(name));
      Function<RC,Optional<IM>> one= rc -> find(ms, m -> m.sig.rc.get() == rc);
      var rc= rcc.rc.map(r -> r == iso ? imm : noH(r)).orElse(imm);
      var order= rc == read ? list(read, imm, mut) : rc == mut ? list(mut, read, imm) : list(imm, read, mut);
      return favorite.map(one).orElseGet(() -> ms.size() == 1 ? of(ms.getFirst()) : order.stream().flatMap(r -> one.apply(r).stream()).findFirst()); }
    Optional<MSigL> methodHeader(RCC rcc, MName name, Optional<RC> favorite){ var d= from(rcc.c.name);
      return methodHeaderIM(rcc, name, favorite).map(m -> new MSigL(m.sig.rc.get(), push(B.xs(d.bs), B.xs(m.sig.bs.get())), d.bs, rcc.c.ts, m.sig.bs.get(), m.sig.ts, m.sig.ret)); }
    static void updateG(IGamma g, String x, IT t2){ var t1= g.get(x); var t= t1 instanceof U ? t2
        : t1 instanceof RCC(var aRc, var aC) && t2 instanceof RCC(var bRc, var bC) && aC.name.equals(bC.name) ? new RCC(aRc.isEmpty() ? bRc : bRc.isEmpty() ? aRc : of(glbRcNoH(aRc.get(), bRc.get())), aC)
        : t1 instanceof RCX a && t2 instanceof RCX(var bRc, var bX) && a.x.equals(bX) ? a.withRC(glbRcNoH(a.rc, bRc)) : null;
      if (t != null){ g.fs.get(g.at(x)).vars.put(x, t); } } static RC glbRcNoH(RC a, RC b){ a = noH(a); b = noH(b);
      return a == b || b == read ? a : a == read ? b : iso; } IE nextT(Type t){ return t.t instanceof U ? t.withT(preferred(t.type)) : t; }
    IE nextC(List<B> bs, IGamma g, Call c){ var e= nextStar(bs, g, c.e);
      if (!(e.t() instanceof RCC rcc) || methodHeader(rcc, c.name, c.rc).isEmpty()){ return c.withEEs(e, nextStar(bs, g, c.es)); }
      var m= methodHeader(rcc, c.name, c.rc).get(); var nCls= m.clsArgs.size();
      var all0= decidedThen(c, m, c.es, Stream.of()); var m0= m.withClsArgs(normToBounds(bs, m.clsBs, all0.subList(0, nCls)));
      var es= nextStar(bs, g, meetWithTargs(c.es, m0, normToBounds(bs, m.methBs, all0.subList(nCls, all0.size()))));
      var all= decidedThen(c, m, es, zip(m.ps0, es, (p,e2) -> refine(m.xs, p, e2.t())).stream()); var clsTs= normToBounds(bs, m.clsBs, all.subList(0, nCls));
      var targs= normToBounds(bs, m.methBs, all.subList(nCls, all.size())); e = meet(e, rcc.withTs(clsTs)); var m1= m.withClsArgs(clsTs);
      var it= meet(c.t, m1.inst(m1.ret0, targs)); var es1= meetWithTargs(es, m1, targs);
      if (e == c.e && es1 == c.es && targs.equals(c.targs) && it.equals(c.t)){ return c; } return new Call(e, c.name, of(c.rc.orElse(m1.rc)), targs, es1, it, c.written);
    } List<IT> decidedThen(Call c, MSigL m, List<IE> es, Stream<List<IT>> argRefinements){ var targs= MSigL.fixTargs(c.targs, m.methBs.size());
      var all= meet(cat(Stream.of(push(m.clsArgs, targs)), argRefinements, Stream.of(refine(m.xs, m.ret0, c.t))).toList());
      var written= push(m.clsArgs, c.written ? targs : qMarks(m.methBs.size()));
      var fromLiterals= IntStream.range(0, es.size()).filter(i -> es.get(i) instanceof Literal).mapToObj(i -> refine(m.xs, m.ps0.get(i), es.get(i).t()));
      var hard= meet(Stream.concat(Stream.of(qMarks(written.size())), fromLiterals).toList());
      var fixed= zip(written, hard, (w,h) -> decided(w) ? w : h); return zip(fixed, all, (b,r) -> decided(b) ? b : r); }
    static boolean decided(IT t){ return t.isTV() && !(t instanceof RCC(var rc, _) && rc.isEmpty()); } Optional<RCC> preciseSelf(Literal l){
      if (l.infName && l.rc.isEmpty()){ return empty(); } return of(l.self(l.rc)); }
    IE nextL(List<B> bs, IGamma g, Literal l){ var selfPrecise= preciseSelf(l); if (!l.infHead){ var cs0= l.cs;
        var selfSuper= cs0.size() != 1 ? selfPrecise : selfPrecise.map(p -> new RCC(p.rc, cs0.getFirst()));
        l = l.infName ? selfSuper.map(l::withT).orElse(l) : l.withT(selfPrecise.get()); if (!(l.t instanceof RCC(_, var c))){ return l; }
        l = l.infName && !c.name.equals(l.name) ? expandLiteral(l, c, bs) : expandDeclaration(l, true); }
      if (!(l.t instanceof RCC rcc)){ return l; } var res= new ArrayList<IM>(); var ts= rcc.c.ts; for (var mi : l.ms){
        var rcci= boundedTs(rcc, ts); var next= mi.e.isEmpty() ? header(rcci, mi) : nextM(bs, g, l, selfPrecise, rcci, mi);
        ts = meet(ts, next.ts); res.add(next.m); } var ms= same(l.ms, res);
      if (ms == l.ms && ts.equals(rcc.c.ts)){ return commitToTable(g, bs, l, rcc); } var t= boundedTs(rcc, ts);
      return commitToTable(g, bs, l.withMsT(ms, t), t); } IE commitToTable(IGamma g, List<B> bs, Literal l, RCC rcc){ var name= l.name;
      if (!rcc.isTV() || !all(l.ms, m -> m.sig.ret.isTV() && all(m.sig.ts, IT::isTV)) || cache.containsKey(name)){ return l; }
      var localBs= cat(ftvMs(g, l.ms), ftvCs(l.cs), rcc.ftv()).distinct().map(x -> B.get(bs, x)).toList(); var newName= name.withArity(localBs.size());
      var ms= name.equals(newName) ? l.ms : same(l.ms, map(l.ms, mi -> !mi.sig.origin.get().equals(name) ? mi : mi.withSig(mi.sig.withOrigin(newName))));
      var orc= l.rc.or(rcc::rc).map(Methods::noH); var orcc= new RCC(orc, rcc.c);
      if (all(l.ms, m -> m.e.isEmpty()) && l.infHead && from(rcc.c.name) != null){ return new Type(orcc, preferred(orcc)); }
      var selfInferred= rcc.c.name.equals(l.name);
      var cs= ToCore.distinctTypes(localBs, selfInferred ? fetchCs(rcc.c) : push(rcc.c, fetchCs(rcc.c))); checkMagicSupertypes(l, cs);
      l = new Literal(orc, newName, localBs, cs, l.thisName, ms, rcc, l.infName, l.infHead);
      if (selfInferred){ l = l.withT(preciseSelf(l).get()); } register(l); return l; } record TSM(List<IT> ts, IM m){} TSM header(RCC rcc, IM m){
      var sig= m.sig; var omh= methodHeaderIM(rcc, sig.m.get(), sig.rc); if (omh.isEmpty()){ return new TSM(rcc.c.ts, m); }
      var rcc0= boundedTs(rcc, refineHeader(rcc, sig, omh.get().sig));
      return new TSM(dropMethBs(rcc0.c.ts, B.xs(sig.bs.get())), m.withSig(headerSig(rcc0, sig))); }
    TSM nextM(List<B> bs, IGamma g, Literal l, Optional<RCC> selfPrecise, RCC rcc, IM m){ var litBs= l.infName ? bs : l.bs;
      g.fs.add(new IGamma.Frame(m.sig.rc.get(), litBs, new HashMap<>()));
      g.declare(l.thisName, selfPrecise.<IT>map(s -> new RCC(s.rc.map(RC::isoToMut), s.c)).orElse(U.Instance));
      g.fs.add(new IGamma.Frame(m.sig.rc.get(), litBs, new HashMap<>()));
      for (int i= 0; i < m.xs.size(); i++){ g.declare(m.xs.get(i), m.sig.ts.get(i)); }
      var e= nextStar(push(litBs, m.sig.bs.get()), g, meet(m.e.get(), m.sig.ret));
      var args= zip(m.xs, m.sig.ts, (x,t) -> x.equals("_") ? t : meet(t, g.get(x))); g.fs.removeLast();
      g.fs.removeLast(); var h= header(rcc, m.withSig(m.sig.withTsT(args, meet(m.sig.ret, e.t())))); var sig= h.m.sig;
      var e1= meet(e, sig.ret); return new TSM(h.ts, sig.equals(m.sig) && e1 == m.e.get() ? m : new IM(sig, m.xs, of(e1))); }
    List<IT> refineHeader(RCC rcc, ISig improvedSig, ISig imh){ var Xs= B.xs(from(rcc.c.name).bs);
      var byArg= zip(imh.ts, improvedSig.ts, (t,it) -> refine(Xs, t, it)); var fromBody= meet(push(byArg, refine(Xs, imh.ret, improvedSig.ret)));
      return zip(rcc.c.ts, fromBody, this::keepDecided); } IT keepDecided(IT decided, IT fromBody){
      var decidedIso= decided instanceof RCX(var aRc, _) && aRc == iso;
      if (xName(decided).isPresent() && xName(decided).equals(xName(fromBody)) && !decidedIso){ return decided; }
      if (!(decided instanceof RCC(var aRc, var aC) && fromBody instanceof RCC b)){ return meet(decided, fromBody); }
      if (!aC.name.equals(b.c.name)){ var asDecided= adaptedSuperTs(b, aC.name);
        return asDecided.isEmpty() ? decided : keepDecided(decided, asDecided.getFirst()); }
      return b.withRCTs(aRc.or(b::rc), zip(aC.ts, b.c.ts, this::keepDecided)); } ISig headerSig(RCC rcc, ISig improvedSig){
      var h= methodHeader(rcc, improvedSig.m.get(), improvedSig.rc).get(); var xs= toXs(B.xs(improvedSig.bs.get()));
      return improvedSig.withTsT(map(h.ps0, p -> h.inst(p, xs)), h.inst(h.ret0, xs)); }
    List<IT> dropMethBs(List<IT> ts, List<String> methBs){ if (methBs.isEmpty()){ return ts; }
      return map(ts, t -> t instanceof RCC rcc ? boundedTs(rcc, dropMethBs(rcc.c.ts, methBs)) : xName(t).filter(methBs::contains).isPresent() ? U.Instance : t);
    } List<IT> refine(List<String> xs, IT t, IT t1){ if (t1 instanceof U){ return qMarks(xs.size()); } return switch (t){
        case X x -> { var n= xs.indexOf(x.name); yield IntStream.range(0, xs.size()).<IT>mapToObj(i -> i == n ? t1 : U.Instance).toList(); }
        case RCX(_, var x) -> refine(xs, x, switch (t1){ case RCX(_, var x1) -> x1;
          case ReadImmX(var x1) -> x1; case RCC(_, var c) -> new RCC(empty(), c); default -> t1; });
        case ReadImmX(var x) -> refine(xs, x, t1 instanceof ReadImmX(var x1) ? x1 : t1); case RCC rcc -> propagateXs(xs, rcc, t1);
        case U _ -> qMarks(xs.size()); }; } boolean isSuper(TName a, TName b){ var d= from(b); return d != null && has(d.cs, a); }
    List<RCC> adaptedSuperTs(RCC src, TName target){ var d= from(src.c.name); if (d == null){ return list(); }
      return d.cs.stream().filter(sc -> sc.name.equals(target)).distinct()
        .map(ci -> (RCC)rename(new RCC(src.rc, ci), B.xs(d.bs), src.c.ts)).toList(); } List<IT> propagateXs(List<String> xs, RCC r, IT t1){
      if (!(t1 instanceof RCC cc)){ return qMarks(xs.size()); } var c= r.c; if (!cc.c.name.equals(c.name)){ var supOk= adaptedSuperTs(cc, c.name);
        if (!supOk.isEmpty()){ return propagateXs(xs, r, supOk.getFirst()); } var subOk= adaptedSuperTs(r, cc.c.name);
        if (!subOk.isEmpty()){ return propagateXs(xs, subOk.getFirst(), t1); } return qMarks(xs.size()); }
      var res= zip(c.ts, cc.c.ts, (t,ti) -> t instanceof RCC rr && !(ti instanceof RCC ci && ci.c.name.equals(rr.c.name)) ? qMarks(xs.size()) : refine(xs, t, ti));
      return res.isEmpty() ? qMarks(xs.size()) : meet(res); } IE ascribe(IE arg, IT expected, boolean receiver){ if (!(expected instanceof RCC exp)){ return arg; }
      return switch (arg){ case Call c -> c.withEEs(ascribe(c.e, expected, true), c.es);
        case Literal l when l.infHead || !l.infName || !l.cs.isEmpty() || !(l.t instanceof U) -> arg;
        case Literal l when !receiver || implementable(exp.c.name) -> l.withT(new RCC(exp.rc, new C(exp.c.name, qMarks(exp.c.ts.size()))));
        case Literal l -> { var res= new Literal(of(imm), l.name, l.bs, l.cs, l.thisName, l.ms, true);
          yield res.withT(preciseSelf(res).get()); } default -> arg; }; } boolean implementable(TName head){ var d= from(head);
      if (d == null){ return false; } var foreignForbidden= !head.pkgName().equals(p.name) && (!head.isPublic() || has(d.cs, sealed));
      return !foreignForbidden && TypeSystem.hasInstance(d); } static IT normToBound(IT t, EnumSet<RC> allowed){
      if (allowed.size() == 1){ return t.withRC(allowed.iterator().next()); } if (!(t instanceof RCC(var rc, var c))){ return t; }
      if (!(rc.isEmpty() || rc.get() == iso && !allowed.contains(iso))){ return t; }
      return new RCC(allowed.contains(imm) ? empty() : of(read), c); }
    static List<IT> normToBounds(List<B> scope, List<B> bs, List<IT> ts){
      return zip(ts, bs, (ti,bi) -> xName(ti).map(x -> B.get(scope, x).rcs.equals(bi.rcs)).orElse(true) ? normToBound(ti, bi.rcs) : ti); }
    static Optional<String> xName(IT t){ return switch (t){ case X x -> of(x.name); case RCX(_, var x) -> of(x.name);
      case ReadImmX(var x) -> of(x.name); default -> empty(); };} RCC boundedTs(RCC rcc, List<IT> ts){
      var d= from(rcc.c.name); return d == null ? rcc.withTs(ts) : rcc.withTs(zip(ts, d.bs, (ti,bi) -> normToBound(ti, bi.rcs))); }
  }
  record ToCore(List<B> ctx){ IE core(IE exp, IE orig){ return switch (exp){ case IE.X(var name, _) -> new IE.X(name);
      case Type(var type, _) -> new Type((RCC)norm(type)); case Literal le -> literal(le, (Literal)orig); case Call e -> { var o= (Call)orig;
        yield new Call(core(e.e, o.e), e.name, of(e.rc.orElse(imm)), map(o.targs.isEmpty() ? e.targs : o.targs, Frontend::norm), zip(e.es, o.es, this::core), false);
      } };} Literal literal(Literal e, Literal o){ var bs= e.bs; if (e.infName && bs.isEmpty()){ var g= new IGamma();
        bs = cat(ftvCs(e.cs), ftvMs(g, e.ms), ftvMs(g, o.ms)).distinct().map(x -> B.get(ctx, x)).toList(); } var name= e.name.withArity(bs.size());
      var inner= e.infName ? with(bs) : new ToCore(bs);
      var ms= e.ms.stream().map(me -> inner.m(me, me.e.isEmpty() ? me : o.ms.get(me.sig.idx)))
        .map(m -> !m.sig.origin.get().equals(e.name) ? m : m.withSig(m.sig.withOrigin(name))).toList();
      var cs= map(distinctTypes(inner.ctx, o.cs.isEmpty() ? e.cs : push(o.cs, e.cs)), Frontend::normC);
      return new Literal(of(e.rc.orElse(imm)), name, bs, cs, e.thisName, ms, e.infName); }
    static List<C> distinctTypes(List<B> bs, List<C> cs){ var res= new ArrayList<C>();
      for (var c : cs){ if (!any(res, r -> TypeSystem.eqModXRC(bs, norm(new RCC(of(imm), r)), norm(new RCC(of(imm), c))))){ res.add(c); } }
      return res; } ToCore with(List<B> bs){ return new ToCore(push(ctx, bs).stream().distinct().toList()); } IM m(IM e, IM o){ var s= sig(e.sig, o.sig);
      return new IM(s, e.xs, e.e.map(ei -> with(s.bs.get()).core(ei, o.e.get()))); }
    static ISig sig(ISig inf, ISig usr){ var ts= zip(usr.ts, inf.ts, (u,i) -> u instanceof U ? i : u);
      return new ISig(usr.rc.or(inf::rc).orElse(imm), usr.m.or(inf::m).orElse(new MName(".inferenceFailed", ts.size())), usr.bs.or(inf::bs).orElse(list()),
        map(ts, Frontend::norm), norm(usr.ret instanceof U ? inf.ret : usr.ret), usr.origin.or(inf::origin).orElse(inferUnknown), usr.abs, usr.idx); } }
  record Gamma(Gamma tail, String name, IT current){ static final Gamma empty= new Gamma(null, null, null);
    Gamma add(String name, IT t){ return new Gamma(this, name, t); }
    Gamma map(UnaryOperator<IT> f){ return this == empty ? this : new Gamma(tail.map(f), name, current == null ? null : f.apply(current)); }
    IT bind(String x){ return this == empty ? null : name.equals(x) ? current : tail.bind(x); }
    Gamma filterFTV(Literal l, boolean captureFree){
      if (this == empty){ return this; } var rest= tail.filterFTV(l, captureFree);
      var drop= captureFree || current != null && !current.ftv().allMatch(B.xs(l.bs)::contains);
      return new Gamma(rest, name, drop ? null : current); } }
  record MType(RC rc, List<IT> ts, IT t){} enum Mode{
    useRead(iso, readH, mutH, readH), flexy(iso, imm, mutH, readH), hyg(mutH, readH, mutH, readH), strong(iso, imm, iso, imm); final RC m, r, mh, rh;
    Mode(RC m, RC r, RC mh, RC rh){ this.m= m; this.r= r; this.mh= mh; this.rh= rh; }
    RC of(RC rc){ return switch (rc){ case mut -> m; case read -> r; case mutH -> mh; case readH -> rh; default -> rc; }; } }
  record TypeSystem(Function<TName,Literal> decs){ static void allOk(List<Literal> tops, Map<TName,Literal> other){ var map= new HashMap<TName,Literal>();
      tops.forEach(t -> collect(t, map)); var ts= new TypeSystem(n -> from(n, map::get, other)); tops.forEach(l -> ts.litOk(Gamma.empty, l)); }
    static void collect(IE e, HashMap<TName,Literal> map){ if (e instanceof Literal l){ map.put(l.name, l); } e.children().forEach(c -> collect(c, map)); }
    boolean kindOf(List<B> bs, IT t, EnumSet<RC> allowed){ if (!allowed.containsAll(intrinsicRCs(bs, t))){ return false; }
      if (!(t instanceof RCC(_, var c))){ return true; } var params= decs.apply(c.name).bs;
      return all(zip(c.ts, params, (ti,p) -> kindOf(bs, ti, p.rcs)), v -> v); }
    void kind(List<B> bs, IT t){ kind(bs, t, allRC); } void kind(List<B> bs, IT t, EnumSet<RC> allowed){ ck(!kindOf(bs, t, allowed)); }
    static EnumSet<RC> intrinsicRCs(List<B> bs, IT t){ return switch (t){ case RCC(var rc, _) -> EnumSet.of(rc.get());
      case RCX(var rc, _) -> EnumSet.of(rc); case X(var x) -> B.get(bs, x).rcs; case U _ -> throw new Fail(); case ReadImmX(var x) -> {
        var rcs= intrinsicRCs(bs, x);
        yield isoImm.containsAll(rcs) ? EnumSet.of(imm) : EnumSet.of(mut, mutH, read, readH).containsAll(rcs) ? EnumSet.of(read) : EnumSet.of(read, imm);
      } };} Gamma vpaOf(Gamma g, Literal l, IM m){
      return g.map(t -> { if (m.sig.rc.get() == imm || kindOf(l.bs, t, isoImm)){ return t.withRC(imm); } if (m.sig.rc.get() == read){
          if (t.explicitRC().stream().anyMatch(r -> r == mut || r == read)){ return t.withRC(read); }
          if (t instanceof X || t instanceof ReadImmX){ return t.readImm(); } }
        return kindOf(l.bs, t, EnumSet.of(imm, mut, read)) ? t : t.readImm(); }); } Gamma discard(Gamma g, Literal l){
      return g.map(t -> { var drop= !kindOf(l.bs, t, allRC) || !kindOf(l.bs, t, noHyg) || l.rc.get().isIsoOrImm() && !kindOf(l.bs, t, isoImm);
        return drop ? null : t; }); } boolean isSub(List<B> bs, IT t1, IT t2){ return t1.equals(t2)
        || t2 instanceof ReadImmX(var x2) && t1 instanceof X x && x2.name.equals(x.name) && kindOf(bs, x, noHyg)
        || isSameShapeSubtype(bs, t1, t2)
        || t1 instanceof RCC(var rc1, var c1) && any(decs.apply(c1.name).cs, ci -> isSub(bs, rename(new RCC(rc1, ci), B.xs(decs.apply(c1.name).bs), c1.ts), t2));
    } List<IT> typeOf(List<B> bs, Gamma g, IE e, List<IT> rs){ return switch (e){ case IE.X x -> {
        var t= g.bind(x.name); ck(t == null); yield reqs(bs, t, rs, false); } case Type t -> {
        kind(bs, t.type); var ll= decs.apply(t.type.c.name); ck(!hasInstance(ll)); var rc= t.type.rc.get();
        var getIso= (rc.isReadOrImm() && !hasAbstractMut(ll)) || rc == mut || rc == mutH; var l= ll.withRC(getIso ? iso : rc);
        l.ms.forEach(m -> checkImplemented(l, m)); yield reqs(bs, getIso ? t.type.withRC(iso) : t.type, rs, true); }
      case Literal l -> checkLiteral(bs, g, l, rs); case Call c -> callTyping(bs, g, c, rs); };}
    static boolean hasInstance(Literal l){ return l.thisName.equals("this") || has(l.cs, captureFree); }
    static long count(String x, IE e, boolean active){ var here= e instanceof IE.X v && v.name.equals(x) ? 1 : 0;
      if (active && e instanceof Literal){ return here; } return here + e.children().mapToLong(c -> count(x, c, active)).sum(); }
    static boolean hasAbstractMut(Literal l){ return any(l.ms, m -> m.sig.abs && m.sig.rc.get() == mut); }
    List<IT> reqs(List<B> bs, IT got, List<IT> rs, boolean rccOnly){ if (rs.isEmpty()){ return list(got); }
      ck(rccOnly && any(rs, r -> !(r instanceof RCC))); return map(rs, r -> isSub(bs, got, r) ? got : null); }
    List<IT> checkLiteral(List<B> bs1, Gamma g, Literal _l, List<IT> rs){ var selfNamed= !_l.thisName.equals("_"); var cf= has(_l.cs, captureFree);
      var getIso= ((_l.rc.get().isReadOrImm() && !hasAbstractMut(_l) && !selfNamed) || _l.rc.get() == mut) && captureFree(_l.bs, g.filterFTV(_l, cf), _l);
      var l= getIso ? _l.withRC(iso) : _l;
      ck(any(rs, r -> !(r instanceof RCC)));
      ck(any(l.ms, m -> m.sig.origin.get().equals(inferUnknown)) || any(l.cs, c -> any(c.ts, TypeSystem::mentionsInferUnknown)));
      var thisType= l.self(l.rc); kind(bs1, thisType); litOk(discard(g.filterFTV(l, cf), l), l);
      ck(selfNamed && count(_l.thisName, _l, false) == 0); ck(any(l.ms, m -> m.e.isPresent() && !hasInstance(l) && !callable(l.rc.get(), m.sig.rc.get())));
      l.ms.forEach(m -> checkImplemented(l, m)); return reqs(bs1, thisType, rs, false); }
    static boolean captureFree(List<B> bs, Gamma g, IE e){ if (!(e instanceof IE.X x)){ return e.children().allMatch(c -> captureFree(bs, g, c)); }
      return g.bind(x.name) == null || all(intrinsicRCs(bs, g.bind(x.name)), RC::isIsoOrImm); }
    static boolean mentionsInferUnknown(IT t){ return t instanceof RCC(_, var c) && (c.name.equals(inferUnknown) || any(c.ts, TypeSystem::mentionsInferUnknown)); }
    void checkImplemented(Literal l, IM m){ ck(m.sig.abs && callable(l.rc.get(), m.sig.rc.get())); }
    static boolean callable(RC litRC, RC recRc){ return recRc != mut || !litRC.isReadOrImm(); } void litOk(Gamma g, Literal l){
      if (has(l.cs, baseId)){ var m= l.ms.getFirst(); var isId= switch (m.e.orElse(null)){ case null -> true;
          case IE.X(var name, _) -> name.equals(m.xs.getFirst());
          case Call c -> c.e instanceof IE.X(var recv, _) && recv.equals(m.xs.getFirst()) && c.name.equals(new MName(".as", 1))
            && m.sig.ts.getFirst() instanceof RCC(_, var cc) && has(decs.apply(cc.name).cs, baseContainer); default -> false; }; ck(!isId); }
      var delta= l.bs; for (var c : l.cs){ kind(delta, new RCC(of(imm), c)); ck(!hasInstance(decs.apply(c.name))); } var sources= new ArrayList<ISig>();
      for (var parent : l.cs){ var parentDef= decs.apply(parent.name); for (var m : parentDef.ms){
          if (!m.sig.origin.get().equals(parentDef.name)){ continue; } var s= m.sig; var canonical= findCanonical(l, s.m.get(), s.rc.get()).bs.get();
          var mapXs= B.xs(push(s.bs.get(), parentDef.bs)); var mapTs= push(toXs(B.xs(canonical)), parent.ts);
          sources.add(s.subst(canonical, mapXs, mapTs));
        } } for (var m : l.ms){ if (m.sig.origin.get().equals(l.name)){ sources.add(m.sig); } }
      group(sources, s -> new RCMName(s.rc, s.m.get())).forEach((k,sigs) -> { var chosen= findCanonical(l, k.name, k.rc.get()); var ctx= push(l.bs, chosen.bs.get()); for (var s : sigs){
          for (int i= 0; i < chosen.ts.size(); i++){ ck(!sameOuterRC(ctx, chosen.ts.get(i), s.ts.get(i)) || !isSub(ctx, s.ts.get(i), chosen.ts.get(i))); }
          ck(!sameOuterRC(ctx, chosen.ret, s.ret) || !isSub(ctx, chosen.ret, s.ret)); } });
      var g1= g.add(l.thisName, l.self(of(l.rc.get().isoToMut()))); for (var m : l.ms){ var g2= vpaOf(g1, l, m);
        var allBs= push(delta, m.sig.bs.get()); m.sig.ts.forEach(t -> kind(allBs, t)); kind(allBs, m.sig.ret); if (m.e.isEmpty()){ continue; }
        for (int i= 0; i < m.xs.size(); i++){ g2 = g2.add(m.xs.get(i), m.sig.ts.get(i)); } ck(typeOf(allBs, g2, m.e.get(), list(m.sig.ret)).getFirst() == null);
        for (int i= 0; i < m.xs.size(); i++){ var x= m.xs.get(i); if (kindOf(allBs, m.sig.ts.get(i), EnumSet.of(mut, read, mutH, readH, imm))){ continue; }
          ck(count(x, m.e.get(), true) > 0 && count(x, m.e.get(), false) != 1); }
      } } static ISig findCanonical(Literal l, MName name, RC rc){ return l.ms.stream().map(IM::sig).filter(s -> s.m.get().equals(name) && s.rc.get() == rc).findFirst().get(); }
    static boolean isSameShapeSubtype(List<B> bs, IT t1, IT t2){
      if (!eqModXRC(bs, t1.withRC(mut), t2.withRC(mut))){ return false; } var rcs2= intrinsicRCs(bs, t2);
      return all(intrinsicRCs(bs, t1), r1 -> all(rcs2, r1::isSubType)); } static boolean sameOuterRC(List<B> bs, IT a, IT b){
      return (a instanceof ReadImmX) == (b instanceof ReadImmX) && a.explicitRC().equals(b.explicitRC()) || eqModXRC(bs, a, b); }
    static boolean eqModXRC(List<B> bs, IT a, IT b){ if (a.equals(b)){ return true; }
      if (!(a instanceof RCC(var aRc, var aC) && b instanceof RCC(var bRc, var bC))){
        if (!(a.withRC(imm) instanceof RCX(_, var x)) || !a.withRC(imm).equals(b.withRC(imm))){ return false; }
        return B.get(bs, x.name).rcs.size() == 1 && intrinsicRCs(bs, a).equals(intrinsicRCs(bs, b)); }
      return aRc.equals(bRc) && aC.name.equals(bC.name) && all(zip(aC.ts, bC.ts, (x,y) -> eqModXRC(bs, x, y)), v -> v); }
    List<IT> callTyping(List<B> bs, Gamma g, Call c, List<IT> rs){
      if (!(typeOf(bs, g, c.e, list()).getFirst() instanceof RCC rcc0)){ throw new Fail(); } var d= decs.apply(rcc0.c.name);
      var sig= d.ms.stream().map(IM::sig).filter(s -> s.m.get().equals(c.name) && s.rc.equals(c.rc)).findFirst().orElseThrow(Fail::new);
      ck(sig.bs.get().size() != c.targs.size()); for (int i= 0; i < c.targs.size(); i++){ kind(bs, c.targs.get(i), sig.bs.get().get(i).rcs); }
      var xs= B.xs(push(d.bs, sig.bs.get())); var ts0= push(rcc0.c.ts, c.targs);
      var base= new MType(sig.rc.get(), renameIT(sig.ts, xs, ts0), rename(sig.ret, xs, ts0));
      var app= filter(promotions(bs, base), m -> rcc0.rc.get().isSubType(m.rc)); ck(app.isEmpty());
      var possible= app; for (int i= 0; i < c.es.size(); i++){ var ai= i;
        var reqs= app.stream().map(m -> m.ts.get(ai)).distinct().toList(); var got= typeOf(bs, g, c.es.get(i), reqs);
        ck(all(got, Objects::isNull)); possible = filter(possible, m -> got.get(reqs.indexOf(m.ts.get(ai))) != null); }
      ck(possible.isEmpty()); var candidates= possible;
      if (rs.isEmpty()){ return list(bestUnique(bs, candidates)); } return map(rs, req -> {
        var ok= filter(candidates, m -> isSub(bs, m.t, req)); return ok.isEmpty() ? null : bestUnique(bs, ok); }); }
    IT bestUnique(List<B> bs, List<MType> ms){ var ts= map(ms, MType::t);
      return find(ts, a -> !any(ts, b -> !b.equals(a) && isSub(bs, b, a))).get(); }
    static RC lub(EnumSet<RC> rcs){ return bound(rcs, RC::isSubType); } static RC glb(EnumSet<RC> rcs){ return bound(rcs, (a,b) -> b.isSubType(a)); }
    static RC bound(EnumSet<RC> rcs, BiPredicate<RC,RC> le){ var bs= Stream.of(RC.values()).filter(b -> all(rcs, x -> le.test(x, b))).toList();
      return find(bs, b -> all(bs, o -> le.test(b, o))).get(); } static List<MType> promotions(List<B> d, MType m){
      var out= new LinkedHashSet<MType>(list(m, apply(d, m, flexy, _ -> flexy, flexy), apply(d, m, strong, _ -> strong, strong),
        apply(d, m, useRead, _ -> useRead, hyg), apply(d, m, hyg, _ -> flexy, hyg)));
      for (int i= 0; i < m.ts.size(); i++){ var ii= i; out.add(apply(d, m, flexy, j -> j == ii ? hyg : flexy, hyg)); } return List.copyOf(out); }
    static MType apply(List<B> d, MType m, Mode rcM, IntFunction<Mode> tsM, Mode retM){
      return new MType(rcM.of(m.rc), IntStream.range(0, m.ts.size()).mapToObj(j -> modeF(d, m.ts.get(j), tsM.apply(j), TypeSystem::glb)).toList(), modeF(d, m.t, retM, TypeSystem::lub)); }
    static IT modeF(List<B> d, IT t, Mode mode, Function<EnumSet<RC>,RC> f){ return switch (t){ case RCC rcc -> rcc.withRC(mode.of(rcc.rc.get()));
        case RCX rcx -> rcx.withRC(mode.of(rcx.rc)); case X x -> modeVar(d, x, rc -> rc, mode, f, t);
        case ReadImmX(var x) -> modeVar(d, x, RC::readImm, mode, f, t); case U _ -> t; }; }
    static IT modeVar(List<B> d, X x, UnaryOperator<RC> inst, Mode mode, Function<EnumSet<RC>,RC> f, IT original){
      var rcs= EnumSet.copyOf(map(B.get(d, x.name).rcs, inst)); if (all(rcs, rc -> mode.of(rc) == rc)){ return original; }
      return new RCX(f.apply(EnumSet.copyOf(map(rcs, mode::of))), x); } } }