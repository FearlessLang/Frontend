package compact;
import static compact.Frontend.TK.*;
import static compact.Frontend.RC.*;
import static compact.Frontend.Mode.*;
import static compact.Util.*;
import compact.Frontend.IT.*;
import compact.Frontend.IE.Call;
import compact.Frontend.IE.Type;
import java.math.*;
import java.util.*;
import java.util.function.*;
import java.util.regex.Pattern;
import java.util.stream.*;
public final class Frontend{ @SuppressWarnings("serial") public static final class Fail extends RuntimeException{} static void ck(boolean b){ if(b) throw new Fail();}
  public static Object parse(String input){ return new Parser(new Names(list(), list(), list(), null), tokens(input)).group(Parser::file);}
  public static List<Literal> compile(String pkg, Map<String,String> override, Map<String,String> files,List<Literal> otherLits){
    var other= otherLits.stream().collect(Collectors.toMap(Literal::name,d -> d)); var raw=new TreeMap<String,File>();
    files.forEach((path, content)-> raw.put(path,(File)parse(content)));
    var heads= filter(raw.keySet(), p -> p.matches("(.*/)?_rank_[^/]*\\.[^/]*"));
    ck(heads.size()!=1); var head= raw.get(heads.get(0));
    ck(any(raw.values(), f -> f != head && f.maps.size()+f.uses.size()>0));
    var ds= flat(raw.values(), f -> f.decs.stream()); var uses= map(head.uses, File.Use::out);
    var decNames= flat(ds,d -> d.owner.decs.stream()); ck(dup(decNames)); var decStrs= map(decNames,TName::s);
    ck(!Collections.disjoint(decStrs, uses)); ck(ds.stream().flatMap(d -> d.owner.gen.used.stream()).anyMatch(x -> decStrs.contains(x)|| uses.contains(x)));
    var map=new HashMap<>(override); for(var u : head.uses){ var p= map.getOrDefault(u.in.pkg(), u.in.pkg());
      var in=p + "." + u.in.simple(); map.put(u.out,in);
      var dom=p.equals(pkg)? decNames.stream().map(n -> n.qualify(pkg)): other.keySet().stream();
      ck(dom.noneMatch(e -> e.s.equals(in))); } var ctx=new Methods(new Pkg(pkg,map, ds,new HashSet<>(decNames)), other);
    var res= ctx.steps(ctx.headers(lower(ctx))); TypeSystem.allOk(res, other); return res; } public enum RC{
    imm, mut, read, iso, mutH, readH; boolean isSubType(RC other){ return this == other || other == readH || this == iso || other == read && !isH() || this == mut && other == mutH;}
    boolean isH(){ return this == mutH || this == readH;} boolean readOnly(){ return this == read || this == imm;}
    boolean isoImm(){ return this == iso || this == imm;} RC isoToMut(){ return this == iso ? mut : this;}
    RC readImm(){ return isoImm()? imm : read;} } public record TName(String s,int arity){
    TName qualify(String pkg){ return new TName(pkg+"."+s,arity);}
    TName arity(int arity){ return new TName(s,arity);}
    String pkg(){ return s.replaceFirst("^(?![a-z]).*|\\..*", "");}
    String simple(){ return s.replaceFirst("^[a-z][^.]*\\.", "");} boolean visible(){ return !simple().startsWith("_"); }}
  public record MName(String s,int arity){ MName arity(int arity){ return new MName(s,arity);} }
  public record B(String x, Set<RC> rcs){ static List<String> xs(List<B> bs){ return map(bs,B::x);}
    static B get(List<B> bs,String name){ return find(bs,b -> b.x.equals(name)); }}
  enum TK{
    Ws("\\s+"), LineComment("//[^\\n]*"), BlockComment("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"),
    Arrow("->"), ORound("\\("), CRound("\\)"), OCurly("\\{"), CCurlyId("\\}[A-Za-z0-9_]+'*"), CCurly("\\}"),
    OSquareArg("(?<=[A-Za-z0-9_'`\""+TK.op+"])(?<!\\*/)\\["), CSquare("\\]"),
    Underscore("_"),Comma(","), SemiColon(";"), ColonColon("::"), Colon(":"), Eq("="), SQuote("'"), ReadImm("read/imm"), RCap("readH|mutH|imm|iso|read|mut"),
    SignedFloat("[+-]"+TK.flt), UnSignedFloat(TK.flt), SignedInt("[+-]"+TK.nat),UnsignedInt(TK.nat), UStr("\"[^\"\\n]*\""), SStr("`[^`\\n]*`"),
    DotName("\\._*[a-z]"+TK.id), UppercaseId("(?:"+TK.pkg+"\\.)?_*[A-Z]"+TK.id),
    LowercaseId("_*[a-z]"+TK.id), BadSStrQuote("'(?:(?!//|/\\*)[^'\\n\"`])*'(?![_a-z])"), Op("(?:(?!/\\*|\\*/|//)["+TK.op+"])+"),
    _EOF(""), _SOF(""), _CurlyGroup(""), _SquareGroup(""), _RoundGroup("");
    static final String pkg="(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*", id="[A-Za-z0-9_]*'*",
      op="\\\\/#*\\-+%<>=!&^~?|", nat="[0-9](?:[0-9_]*[0-9])?",flt= nat+"\\."+nat+"(?:[eE][+-]?"+nat+")?(?:soft)?"; final Pattern p;
    TK(String regex){ p= Pattern.compile(regex);}
    int match(String s,int i){ var m=p.matcher(s).useTransparentBounds(true).region(i,s.length()); return m.lookingAt()? m.end()-i :-1;} }
  static boolean matches(String input, TK... kinds){ return any(list(kinds), k -> k.match(input,0)== input.length()); }
  static final TK[] typeName={UppercaseId, SignedFloat, UnSignedFloat, SignedInt,UnsignedInt,SStr, UStr};
  record Token(TK kind,String content,List<Token> tokens){ boolean is(TK... kinds){ return list(kinds).contains(kind);} }
  static final String allowed="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>,.;:()[]{}`'\"!?@#$%^&_|~\\ \n";
  static final Map<TK,Map<TK,TK>> groups= Map.of(_SOF, Map.of(_EOF,_EOF), ORound, Map.of(CRound,_RoundGroup), OSquareArg, Map.of(CSquare,_SquareGroup), OCurly, Map.of(CCurly,_CurlyGroup, CCurlyId,_CurlyGroup));
  static List<Token> tokens(String s){ s = s.replaceFirst("^\\uFEFF", "").replaceAll("[\\r\\u2028\\u2029\\u0085]", "\n");
    ck(s.codePoints().anyMatch(c -> allowed.indexOf(c)<0)); var res=new ArrayList<Token>(list(new Token(_SOF, "", list()))); for(int i=0;i < s.length();){
      TK best=null; int len=0; for(var k : TK.values()){ var l=k.match(s,i); if(l > len){ best=k; len=l;} } ck(best == null);
      var t=new Token(best,s.substring(i,i+len), list()); i += len;if(t.is(Ws, LineComment, BlockComment)) continue;
      ck(t.is(BadSStrQuote)|| t.is(OSquareArg)&& res.getLast().is(SStr, UStr, SignedInt,UnsignedInt, SignedFloat, UnSignedFloat)); res.add(t);}
    res.add(new Token(_EOF, "", list())); var it=res.iterator(); return list(tree(it,it.next()));} static Token tree(Iterator<Token> it, Token open){
    var out=new ArrayList<Token>(list(open)); while(true){ var c= it.next();
      var g= groups.get(open.kind).get(c.kind); if(g != null){ out.add(c); return new Token(g, "", out);}
      if(groups.containsKey(c.kind)){ out.add(tree(it,c)); continue;} ck(any(groups.values(), m -> m.containsKey(c.kind))); out.add(c);} }
  sealed interface PE{ record X(String name) implements PE{}
    record Lit(String self,List<PM> ms) implements PE{} record Typed(RC rc,C c, Lit l) implements PE{}
    record Declared(RC rc, Declaration dec) implements PE{} record Args(RC rc,List<IT> ts){}
    record Call(PE e,MName name, Args targs, XPat pat,List<PE> es) implements PE{} record Implicit() implements PE{} }
  record PSig(RC rc, MName m, List<B> bs,List<Parameter> ps, IT t){}
  record PM(PSig sig, PE body, boolean implicit){
    PM(PSig sig, PE body){ this(sig, body, body != null && Frontend.implicit(body)); }
    int arity(){ return sig.ps.size()+(implicit ?1 :0);} } static boolean implicit(PE e){ return switch(e){
    case PE.X _, PE.Typed _, PE.Declared _, PE.Lit _ -> false; case PE.Implicit _ -> true;
    case PE.Call c -> implicit(c.e)|| any(c.es,Frontend::implicit); };} record Parameter(XPat xp, IT t){}
  sealed interface XPat{ Stream<String> names();
    record Name(String x) implements XPat{ public Stream<String> names(){ return Stream.of(x);} }
    record Destruct(List<List<MName>> extract,String id) implements XPat{
      public Stream<String> names(){ return extract.stream().map(e -> e.getLast().s.substring(1)+ id);} }}
  record Declaration(TName name,List<B> bs,List<C> cs, PE.Lit l, Owner owner){}
  record File(List<String> maps,List<Use> uses,List<Declaration> decs){ record Use(TName in,String out){} }
  record Names(List<String> xs,List<String>Xs,List<String> hiddenXs, Owner owner){ Names add(List<String> xs,List<String>Xs){
      owner.vars.used.addAll(xs); owner.gen.used.addAll(Xs); return new Names(push(this.xs, xs), push(this.Xs,Xs), hiddenXs, owner);} }
  record Key(RC rc,MName name){} static final class Parser{ Names names; final List<Token> ts; int index=0; int limit;
    Parser(Names names,List<Token> ts){ this.names= names; this.ts= ts; limit= ts.size();}
    Parser make(List<Token> tokens){ return new Parser(names, tokens);} <R> R whole(Function<Parser,R> r){ var res=r.apply(this); ck(!end()); return res;}
    boolean end(){ return limit == index;}
    boolean peek(int la, TK... kinds){ return index+la < limit && ts.get(index+la).is(kinds);}
    boolean peek(TK... kinds){ return peek(0, kinds);} boolean peekIf(Predicate<Token> p){ return !end() && p.test(ts.get(index)); }
    Token expect(TK... kinds){ ck(end()); var t= ts.get(index++); ck(kinds.length >0 && !t.is(kinds)); return t;}
    boolean fwdIf(boolean v){ if(v) index +=1; return v;} <R> R group(Function<Parser,R> r){
      var p= make(ts.get(index++).tokens); p.index=1;p.limit -=1; return p.whole(r);} Parser front(ToIntFunction<Parser> probe){
      var sp= make(ts.subList(index, limit)); int drop= probe.applyAsInt(sp); var res= make(ts.subList(index,index+sp.index-drop)); index += sp.index; return res;}
    <R> List<R> splitBy(ToIntFunction<Parser> probe, Function<Parser,R> elem){ var res=new ArrayList<R>(); while (!end()) res.add(front(probe).whole(elem)); return res;}
    <R> List<R> items(Function<Parser,R> r, ToIntFunction<Parser> probe){ return group(p -> p.splitBy(probe,r)); }
    <R> R prefix(ToIntFunction<Parser> probe, Function<Parser,R> first){ var i=index; var p= front(probe); if (!end()) return p.whole(first); index = i; return null;}
    int splitOn(int mode, TK k){ while (!end()){ if (!expect().is(k)) continue;if(mode ==2) index -=1; return mode &1;} return 0;}
    PE expr(){ return posts(atom()); } PE posts(PE e){ while (!end()) e = post(e); return e;}
    boolean isDec(){ return peek(typeName)&&(peek(1, Colon)|| peek(1,_SquareGroup)&& peek(2, Colon)); }
    PE atom(){ if (peek(LowercaseId)){ var x= expect().content; ck(!names.xs.contains(x)); return new PE.X(x);}
      if (peek(_RoundGroup)) return group(Parser::expr);
      if(fwdIf(peek(ColonColon))) return new PE.Implicit(); if (peek(_CurlyGroup)) return group(p -> p.literal(false));
      var rc= optCap(); ck(rc != null && rc.isH()); if(isDec()) return new PE.Declared(rc, parseDeclaration(false));
      return new PE.Typed(or(rc, imm), constructor(), peek(_CurlyGroup)? group(p -> p.literal(false)): null); }
    RC cap(){ return RC.valueOf(expect(RCap).content);} RC optCap(){ return peek(RCap)? cap(): null;} C constructor(){
      var c=name(); if (!peek(_SquareGroup)) return new C(c,list()); var ts= items(Parser::type, commaSkip);
      return new C(c.arity(ts.size()), ts);} TName name(){ var s= expect(typeName).content;
      ck(names.Xs.contains(s)|| names.hiddenXs.contains(s)); var res=new TName(s,0); ck(!res.pkg().isEmpty() && !res.visible()); return res;}
    IT type(){ if(fwdIf(peek(ReadImm))) return new ReadImmX(variable(false)); var rc= optCap();
      if (peekIf(t -> t.is(typeName)&& !names.Xs.contains(t.content))) return new RCC(or(rc, imm), constructor());
      var res= variable(false); return rc == null ? res : new RCX(rc,res);} X variable(boolean mustNew){
      var c= expect(UppercaseId,"[^.]*"); ck(mustNew ? names.Xs.contains(c)|| names.hiddenXs.contains(c): !names.Xs.contains(c));
      return new X(c);} PE post(PE receiver){ if (peek(SignedFloat, SignedInt)){ var num= expect().content;
        var lit=new PE.Typed(imm,new C(new TName(num.substring(1),0), list()), null);
        return new PE.Call(receiver,new MName(num.substring(0,1),1), null, null, list(lit)); }
      var m=new MName(expect(DotName, Op).content,0); var sq= peek(_SquareGroup)? group(Parser::arguments): null;
      if (peek(_RoundGroup)){ var es= items(Parser::expr, Parser::commaExpr);
        return new PE.Call(receiver,m.arity(es.size()), sq, null, es);}
      var xpat= peek(LowercaseId,_CurlyGroup)&& peek(1, Eq)? pattern(): null; if(xpat != null) expect(Eq);
      if(end() || peek(DotName, Op, Colon)){ ck(xpat != null); return new PE.Call(receiver,m, sq,xpat,list()); }
      var atom= atom(); var xs= xsOf(xpat).toList(); fresh(xs);
      ck(xpat instanceof XPat.Destruct && xs.size()>31); names = names.add(xs,list());
      if(xpat == null) return new PE.Call(receiver,m.arity(1), sq,xpat,list(atom)); return new PE.Call(receiver,m.arity(2), sq,xpat,list(atom, posts(post(new PE.X(""))))); } XPat pattern(){
      if (peek(LowercaseId, Underscore)) return new XPat.Name(binder().name); return group(Parser::destruct);} XPat.Destruct destruct(){
      var id= ts.get(limit).content.substring(1);
      var chains= splitBy(commaSkip,p -> p.splitBy(q -> { q.expect(); return 0; }, q -> new MName(q.expect(DotName).content,0)));
      ck(chains.isEmpty() || any(chains,List::isEmpty)); var res=new XPat.Destruct(chains,id);
      ck(res.names().anyMatch(x -> !matches(x, LowercaseId)|| matches(x,RCap))); return res;} PE.Args arguments(){
      var hasRC= peek(RCap)&& ts.get(index+1).is(Comma, CSquare); var rc= hasRC ? cap(): null;
      if(hasRC && !end()) expect(Comma); return new PE.Args(rc, splitBy(commaSkip, Parser::type)); } PE.X binder(){
      var x= expect(LowercaseId, Underscore).content; ck(names.xs.contains(x)); return new PE.X(x);} PE.Lit literal(boolean top){
      ck(ts.get(limit).is(CCurlyId)); var self= fwdIf(peek(SQuote))? binder().name : null; var n= or(self, top ?"this": "_");
      ck(top && !n.equals("this")); if (!n.equals("_")) names = names.add(list(n), list());
      var ms= splitBy(p -> p.splitOn(1, SemiColon), p -> p.method(top));
      var ns= map(filter(ms,m -> m.sig.m != null), m -> new Key(m.sig.rc, m.sig.m.arity(m.arity()))); ck(dup(ns));
      ck(any(ns, nn -> nn.rc == null && any(ns,o -> o.name.equals(nn.name)&& o.rc != null)));
      ck(dup(map(filter(ms,m -> m.sig.m == null), PM::arity))); return new PE.Lit(self, ms);}
    Stream<String> xsOf(XPat xp){ return Stream.ofNullable(xp).flatMap(XPat::names).filter(x -> !x.equals("_")); }
    void fresh(List<String> xs){ ck(dup(xs)|| any(xs, names.xs::contains)); }
    PM body(PSig sig){ var xs= flat(sig.ps,p -> xsOf(p.xp)); fresh(xs);
      names = names.add(xs, B.xs(or(sig.bs,list()))); var m=new PM(sig, whole(Parser::expr));
      ck(any(sig.ps,p -> p.xp instanceof XPat.Destruct) && xs.size()+ (m.implicit ?1 :0)>32); return m;} PM method(boolean top){
      var m= prefix(p -> p.splitOn(1, Arrow), Parser::signature); if(m != null) return body(m);
      var hasSig= peek(DotName, Op)|| peek(RCap)&& peek(1, DotName, Op); if (!hasSig)return new PM(noSig, whole(Parser::expr));
      var sig= signature(); ck(!top); return new PM(sig, null); } PSig signature(){
      var rc= optCap(); ck(rc != null && (rc.isH() || rc == iso));
      var m= peek(DotName, Op)? new MName(expect().content,0): null; var bs= peek(_SquareGroup)? bounds(true): null;
      names = names.add(list(), B.xs(or(bs,list())));
      var ps= peek(_RoundGroup)? items(Parser::parameter, commaSkip): peek(Colon)? List.<Parameter>of(): splitBy(commaSkip, Parser::parameter);
      var t= fwdIf(peek(Colon))? type(): unknown; ck(!end()); var xs= flat(ps,p -> xsOf(p.xp));
      ck(dup(xs)); return new PSig(rc,m, bs, ps,t);} Parameter parameter(){
      var x= peek(LowercaseId, Underscore,_CurlyGroup)? pattern(): null;
      var p=new Parameter(x,x == null ? type(): fwdIf(peek(Colon))? type(): unknown); ck(!end()); return p;}
    List<B> bounds(boolean mustNew){ var res= items(p -> p.bound(mustNew), Parser::commaBound); ck(dup(B.xs(res))); return res;} B bound(boolean mustNew){
      var x= variable(mustNew).name;if(end()) return new B(x, rcs(imm)); expect(Colon); ck(end()); if (!peek(Op)){
        var rcs= splitBy(commaSkip, Parser::cap); ck(dup(rcs)); return new B(x, EnumSet.copyOf(rcs)); }
      return switch(expect(Op).content){ case "**" -> new B(x, allRC); case "*" -> new B(x, rcs(imm, mut, read));
        default -> throw new Fail(); }; } Declaration parseDeclaration(boolean top){ var c=name(); ck(c.s.contains(".")|| primitive(c.s));
      var bs= peek(_SquareGroup)? bounds(top): List.<B>of(); var Xs=B.xs(bs); var outer= names; var owner= top ? new Owner(): names.owner;
      names = new Names(names.xs,list(), push(names.hiddenXs, names.Xs), owner).add(list(),Xs); c = c.arity(Xs.size()); owner.decs.add(c); expect(Colon);
      var cs= required(prefix(p -> p.splitOn(2,_CurlyGroup), p -> p.splitBy(commaSkip, Parser::constructor))); ck(dup(cs));
      var l= group(p -> p.literal(top)); names = outer; return new Declaration(c, bs, cs,l, owner);} File file(){
      var maps=new ArrayList<String>(); var uses=new ArrayList<File.Use>(); Function<Parser,Object> header=p -> {
        if (!p.peek(LowercaseId)) return ""; ck(!p.ts.get(--p.limit).is(SemiColon)); return p.splitBy(q -> q.splitOn(1, SemiColon), q -> q.directive(maps, uses));
      }; if(prefix(Parser::headEnd, header)== null) whole(header);
      var ds= splitBy(p -> p.splitOn(0,_CurlyGroup), p -> p.parseDeclaration(true)); return new File(maps, uses, ds);}
    String expect(TK kind, String regex){ var s= expect(kind).content; ck(!s.matches(regex)); return s;}
    Object directive(ArrayList<String> maps, ArrayList<File.Use> uses){ if(fwdIf(peekIf(t -> t.content.equals("map")))){
        var in= expect(LowercaseId,TK.pkg); expect(LowercaseId,"as"); expect(LowercaseId,TK.pkg);
        expect(LowercaseId,"in"); var key=in+" "+expect(LowercaseId,TK.pkg); ck(maps.contains(key)); maps.add(key);} else{
        expect(LowercaseId,"use"); var t1=name(); expect(LowercaseId,"as");
        var t2= expect(UppercaseId,"[^.]*"); ck(any(uses,u -> u.in.equals(t1)|| u.out.equals(t2)));
        uses.add(new File.Use(t1,t2)); } ck(!end()); return null;}
    int commaExpr(){ var inColon=false; while (!end()){
        var t= expect(); if(t.is(Comma)&& !inColon)return 1;if (!t.is(_SquareGroup,Comma, UppercaseId)) inColon = false;
        if(t.is(Colon)) inColon = true;} return 0;} int commaBound(){ while (!end()){ if(expect().is(Comma)&& !peek(RCap)) return 1;} return 0;}
    int headEnd(){ while (!(end() || isDec())) expect(); return 0;} static final ToIntFunction<Parser> commaSkip=p -> p.splitOn(1,Comma);}
  record Pkg(String name, Map<String,String> map,List<Declaration> decs, Set<TName> decNames){}
  record Scope(HashSet<String> used, HashMap<String,Integer> seq){ Scope(){ this(new HashSet<>(), new HashMap<>());} }
  record Owner(Scope gen, Scope vars, ArrayList<TName> decs){ Owner(){ this(new Scope(), new Scope(), new ArrayList<>());} }
  record Fresh(Scope top, HashSet<String> reserved, HashMap<TName,Owner> owners,String pkg){
    Fresh(Pkg p){ this(new Scope(), new HashSet<>(), new HashMap<>(), p.name);
      top.used.addAll(map(p.decNames,TName::simple)); top.used.addAll(p.map.keySet());
      for(var d : p.decs){ reserved.addAll(d.owner.gen.used); owners.put(d.name.qualify(pkg), d.owner);} }
    TName type(TName hint,int arity){
      var res=new TName(pkg+"."+fresh(hint.simple(),"ABCDEFGHJKMNPQRSTUVWXYZ", top,list(reserved)),arity); owners.put(res, owners.get(hint)); return res;}
    boolean available(TName owner,String x,List<String> scope){ return !owners.get(owner).gen.used.contains(x)&& !top.used.contains(x)&& !scope.contains(x);}
    String generic(TName owner,String hint,List<String> siblings){
      var cand= fresh(hint,"ABCDEFGHJKMNPQRSTUVWXYZ", owners.get(owner).gen,list(top.used, siblings)); reserved.add(cand); return cand;}
    String variable(TName owner,String hint){ return fresh(hint,"abcdefghjkmnpqrstuvwxyz", owners.get(owner).vars,list()); }
    static String fresh(String hint,String alphabet, Scope s,List<Collection<String>> extraChecks){
      var base= hint.replaceAll("[^A-Za-z0-9]", "").replaceFirst("(?<=.{4}).*", ""); for(int n=s.seq.getOrDefault(base,1);; n +=1){
        var sb=new StringBuilder(); for(int k=n;k >0;k =(k-1)/ alphabet.length()) sb.append(alphabet.charAt((k-1)% alphabet.length()));
        var cand="_"+sb.reverse()+base;if(s.used.contains(cand)|| any(extraChecks,e -> e.contains(cand))) continue;
        s.used.add(cand); s.seq.put(base,n+1); return cand;} }}
  static final TName baseStr=new TName("base.Str",0), baseNat=new TName("base.Nat",0), baseInt=new TName("base.Int",0), baseFloat=new TName("base.Float",0),
    widen=new TName("base.WidenTo",1), sealed=new TName("base.Sealed",0), captureFree=new TName("base.CaptureFree",0), baseId=new TName("base.BaseId",2),
    baseContainer=new TName("base.BaseContainer",1), baseVoid=new TName("base.Void",0);
  static Set<RC> rcs(RC first, RC... rest){ return EnumSet.of(first, rest);}
  static final Set<RC> isoImm= rcs(iso, imm), noHyg= rcs(iso, imm, mut, read), allRC= EnumSet.allOf(RC.class);
  static boolean has(List<C> cs,TName magic){ return any(cs,c -> c.name.equals(magic)); }
  static boolean primitive(String name){ return "+-1234567890\"`".contains(name.substring(0,1)); }
  static Literal from(TName n, Function<TName,Literal> map, Map<TName,Literal> other){ var res= map.apply(n); if(res == null) res = other.get(n);
    if(res != null || !n.pkg().equals("base") || !primitive(n.simple())) return res; var s=n.simple();
    var lit=s.startsWith("`") || s.startsWith("\"") ? baseStr : matches(s,UnsignedInt)? baseNat : matches(s, SignedInt)? baseInt : baseFloat;
    var sup= from(lit,map, other); var ms= map(sup.ms,m -> m.signature(new ISig(m.sig.rc,m.sig.m,m.sig.bs,m.sig.ts,m.sig.ret,n,false,m.sig.idx)));
    return new Literal(imm,n,list(), push(new C(lit,list()), sup.cs),"this", ms,true);}
  static int bits(String s){ return new BigInteger(s.replace("_","")).bitLength();}
  static boolean floatOk(String raw){ var soft= raw.endsWith("soft"); var ns= raw.replace("soft", "").replace("_",""); var d= Double.parseDouble(ns);
    return Double.isFinite(d)&&(soft || (d ==0 ? new BigDecimal(ns.replaceAll("[eE].*", "")): new BigDecimal(ns).subtract(new BigDecimal(d))).signum()==0);}
  static final IT unknown= U.Instance; static final PSig noSig=new PSig(null,null,null,list(), unknown);
  public sealed interface IT{ default boolean isTV(){ return !undecided();}
    default RC explicitRC(){ return null;} default int depth(){ return 1;}
    record X(String name) implements IT{} record RCX(RC rc,X x) implements IT{ public RC explicitRC(){ return rc;} }
    record ReadImmX(X x) implements IT{} record C(TName name,List<IT> ts){ int depth(){ return 1+ts.stream().mapToInt(IT::depth).max().orElse(1);} }
    record RCC(RC rc,C c) implements IT{ public RCC{ if(c.depth() >100) throw new Fail(); } RCC withTs(List<IT> ts){ return with(rc, ts);}
      RCC with(RC rc,List<IT> ts){ var c1=new C(c.name, ts); return c1.depth() >100 ? this : new RCC(rc,c1);}
      public boolean isTV(){ return all(c.ts, IT::isTV);} public int depth(){ return c.depth();}
      public RC explicitRC(){ return rc;} } enum U implements IT{ Instance }
    record Amb(List<IT> cs) implements IT{}
    default boolean undecided(){ return this == unknown || this instanceof Amb;} default IT withRC(RC rc){ return switch(this){
      case RCC(_, var c)-> new RCC(rc,c); case RCX(_, var x)-> new RCX(rc,x); case X x -> new RCX(rc,x);
      case ReadImmX(var x)-> new RCX(rc,x); case U _, Amb _ -> this; };} default Stream<String> ftv(){ return switch(this){ case X(var name)-> Stream.of(name);
      case RCX(_, var x)-> x.ftv(); case ReadImmX(var x)-> x.ftv(); case RCC(_, var c)-> c.ts.stream().flatMap(IT::ftv); case U _, Amb _ -> Stream.of(); };}
    default IT readImm(){ return switch(this){ case X x -> new ReadImmX(x); case ReadImmX _ -> this;
      case RCC(var rc,var c)-> new RCC(rc == null ? null : rc.readImm(), c); case RCX(var rc,var x)-> new RCX(rc.readImm(), x); case U _, Amb _ -> this; };}}
  public sealed interface IE{ IT t(); IE withT(IT t); default Stream<IE> children(){ return switch(this){
      case X _, Type _ -> Stream.of(); case Literal l -> l.ms.stream().flatMap(m -> Stream.ofNullable(m.e)); case Call c -> Stream.concat(Stream.of(c.e), c.es.stream()); };}
    record X(String name, IT t) implements IE{ X(String name){ this(name, unknown);}
      public IE withT(IT t){ return new X(name,t);} }
    record Type(RCC type, IT t) implements IE{ Type(RCC type){ this(type, unknown);}
      public IE withT(IT t){ return new Type(type,t);} }
    record Call(IE e,MName name, RC rc,List<IT> targs,List<IE> es, IT t, boolean written) implements IE{
      Call(IE e,MName name, RC rc,List<IT> targs,List<IE> es, boolean written){ this(e,name, rc,targs, es, unknown, written);}
      Call children(IE e,List<IE> es){ return new Call(e,name,rc,targs, es,t, written);}
      public Call withT(IT t){ return new Call(e,name,rc,targs, es,t, written);} }}
  public record Literal(RC rc,TName name,List<B> bs,List<C> cs,String self,List<IM> ms, IT t, boolean anonymous, boolean expanded) implements IE{
    Literal(RC rc,TName name,List<B> bs,List<C> cs,String self,List<IM> ms, boolean anonymous){
      this(rc,name, bs, cs,self, ms, unknown, anonymous,false);}
    public Literal withT(IT t){ return new Literal(rc,name, bs, cs,self, ms,t, anonymous, expanded);}
    Literal header(List<C> cs,List<IM> ms, boolean ex){ return new Literal(rc,name, bs, cs,self, ms,t, anonymous,ex);}
    RCC self(RC rc){ return new RCC(rc,new C(name, vars(bs))); }
    Literal withRC(RC rc){ return new Literal(rc,name, bs, cs,self, ms, anonymous);} }
  public record IM(ISig sig,List<String> xs, IE e){ IM(ISig sig){ this(sig, Collections.nCopies(sig.ts.size(), "_"), null); }
    IM signature(ISig sig){ return new IM(sig, xs,e);} }
  public record ISig(RC rc,MName m,List<B> bs,List<IT> ts, IT ret,TName origin, boolean abs,int idx){
    ISig types(List<IT> ts, IT ret){ return new ISig(rc,m, bs, ts, ret, origin, abs, idx);}
    ISig origin(TName origin){ return new ISig(rc,m, bs, ts, ret, origin, abs, idx);}
    ISig subst(List<B> bs,List<String> xs,List<IT> ts){ return new ISig(rc,m, bs, renameIT(this.ts, xs, ts), rename(ret, xs, ts), origin, abs, idx);}
  }
  static<T>T or(T a,T b){ return a == null ? b : a;}
  static<T>T required(T a){ ck(a == null); return a;}
  static final class IGamma{
    record Frame(RC rc,List<B> bs, HashMap<String,IT> vars){}
    final ArrayList<Frame> fs=new ArrayList<>(list(new Frame(null,list(), new HashMap<>())));
    int at(String x){ return range(fs.size()).filter(i -> fs.get(i).vars.containsKey(x)).findFirst().orElse(-1);}
    IT get(String x){ var i= at(x); return i == -1 ? null : fs.get(i).vars.get(x);} IT adapted(String x){ var i= at(x); var t=get(x);
      for(var s=i +1;s < fs.size(); s +=1)t = adapt(t, fs.get(s).rc, fs.get(s).bs); return t;} boolean escapes(String x){
      var fxs=get(x).ftv().toList(); return IntStream.range(at(x)+1, fs.size()).anyMatch(s -> !B.xs(fs.get(s).bs).containsAll(fxs)); }
    static IT adapt(IT t, RC rc,List<B> bs){ var x=t instanceof X(var n)? n : t instanceof ReadImmX(X(var n)) ? n : null;if(x != null){
        var xRcs=B.get(bs,x).rcs;if(rc == imm || isoImm.containsAll(xRcs)) return t.withRC(imm); return rc == read || xRcs.contains(iso)? t.readImm(): t;}
      var trc=t.explicitRC(); if(rc == imm || trc == iso)return t.withRC(imm); return rc == read && trc == mut ? t.withRC(read): t;}
    void declare(String x, IT t){ if (!x.equals("_")) fs.getLast().vars.put(x,t);}
    Object snap(){ var m=new HashMap<String,IT>(); fs.forEach(f -> m.putAll(f.vars)); return m;} }
  static C normC(C c){ ck(!all(c.ts, IT::isTV)); return fillC(c);} static IT norm(IT t){ ck(!t.isTV()); return fill(t);}
  static C fillC(C c){ return new C(c.name,map(c.ts,Frontend::fill)); } static IT fill(IT t){ return t instanceof RCC(var rc,var c)? new RCC(or(rc, imm), fillC(c)): t;}
  static IT rename(IT t,List<String> xs,List<IT> ts){ return switch(t){ case X x -> xs.contains(x.name)? ts.get(xs.indexOf(x.name)): x;
      case RCX(var rc,var x)-> rename(x, xs, ts).withRC(rc); case RCC rcc -> rcc.withTs(renameIT(rcc.c.ts, xs, ts));
      case ReadImmX(var x)-> rename(x, xs, ts).readImm(); case U _, Amb _ -> t; }; }
  static List<IT> renameIT(List<IT> tsi,List<String> xs,List<IT> ts){ return map(tsi, ti -> rename(ti, xs, ts)); }
  static List<IT> vars(List<B> bs){ return map(bs,b -> new X(b.x)); }
  static List<IT> qMarks(int n){ return Collections.nCopies(n, unknown);}
  record MSigL(RC rc,List<String> xs,List<B> clsBs,List<IT> clsArgs,List<B> methBs,List<IT> ps0, IT ret0){
    MSigL arguments(List<IT> clsArgs){ return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0);}
    IT inst(IT t,List<IT> targs){ return rename(t, xs, push(clsArgs, fixTargs(targs, methBs.size())));}
    static List<IT> fixTargs(List<IT> targs,int n){ return targs.size()> n ? targs.subList(0,n): push(targs,qMarks(n-targs.size())); }}
  static Stream<String> ftvE(IGamma g, IE e){ return switch(e){
    case IE.X(var name,var t)-> Stream.concat(t.ftv(), Stream.ofNullable(g.get(name)).flatMap(IT::ftv));
    case Literal l -> cat(l.bs.stream().map(B::x), ftvCs(l.cs), ftvMs(g,l.ms));
    case Call(var ei, _, _, var targs,var es, _, _) -> cat(ftvE(g, ei), targs.stream().flatMap(IT::ftv), es.stream().flatMap(x -> ftvE(g,x)));
    case Type(var t, _) -> t.ftv(); };}
  static Stream<String> ftvCs(List<C> cs){ return cs.stream().flatMap(c -> c.ts.stream().flatMap(IT::ftv)); }
  static Stream<String> ftvMs(IGamma g,List<IM> ms){ return ms.stream().flatMap(m -> { var domBs=B.xs(or(m.sig.bs,list()));
      return cat(m.sig.ts.stream().flatMap(IT::ftv), m.sig.ret.ftv(), Stream.ofNullable(m.e).flatMap(ei -> ftvE(g, ei))).filter(x -> !domBs.contains(x));
    }); } static IE copy(Fresh fresh, IE e){ return switch(e){ case IE.X(var name,var t)-> new IE.X(name,t);
    case Type(var type,var t)-> new Type(type,t);
    case Call c -> new Call(copy(fresh,c.e), c.name,c.rc,c.targs,map(c.es,x -> copy(fresh,x)), c.t,c.written);
    case Literal l -> { ck(!l.anonymous); var newName= fresh.type(l.name,l.name.arity);
      yield new Literal(l.rc,newName,l.bs,l.cs,l.self,map(l.ms,m -> copyM(fresh,m,l.name,newName)), l.t,true,l.expanded);
    }};} static IM copyM(Fresh fresh, IM m,TName oldName,TName newName){
    var sig= Objects.equals(m.sig.origin, oldName)? m.sig.origin(newName): m.sig;
    return new IM(sig,m.xs,m.e == null ? null : copy(fresh, m.e)); } static List<Literal> lower(Methods meths){ var v=new Visitor(meths);
    for(var di : meths.p.decs){ v.owner = v.f(di.name); v.addDeclaration(v.owner, mut, di,true);} return v.decs;} record XE(String x, PE e){}
  static final class Visitor{ final Methods meths; TName owner; final ArrayList<String> implicits=new ArrayList<>(); final ArrayList<Literal> decs=new ArrayList<>();
    Visitor(Methods meths){ this.meths= meths;} TName f(TName tn){ var p= meths.p; var pN= tn.pkg(); if(pN.isEmpty() && primitive(tn.s)) return tn.qualify("base");
      var full=new TName(pN.isEmpty()? p.map.getOrDefault(tn.s,p.name+"."+tn.s): p.map.getOrDefault(pN,pN)+"."+tn.simple(), tn.arity);
      ck(!(full.pkg().equals(p.name)? p.decNames.contains(new TName(full.simple(), full.arity)): meths.other.containsKey(full))); return full;}
    IT visitT(IT t){ return t instanceof RCC(var rc,var c)? new RCC(rc, visitC(c)): t;} IE visitE(PE e){ return switch(e){
        case PE.X x -> new IE.X(x.name); case PE.Implicit _ -> new IE.X(implicits.getLast());
        case PE.Typed t -> t.l == null ? new Type(new RCC(t.rc, visitC(t.c))) : liftLiteral(t.rc,list(visitC(t.c)), t.l);
        case PE.Declared c -> { var name=f(c.dec.name); meths.fresh.owners.put(name, meths.fresh.owners.get(owner));
          yield addDeclaration(name,or(c.rc, imm), c.dec,false);} case PE.Lit l -> liftLiteral(null,list(), l); case PE.Call c0 -> {
          var c=c0.pat != null ? desugarCPat(c0): c0; var recv= visitE(c.e); var es= map(c.es,this::visitE);
          var sq= or(c.targs,new PE.Args(null, list()));
          yield new Call(recv,c.name,sq.rc, map(sq.ts,this::visitT), es,c.targs != null); } }; } C visitC(C c){ var s=c.name.s;
      var bad= primitive(s)&&(matches(s,UnsignedInt)&& bits(s)>64 || matches(s, SignedInt)&& bits(s)>63
        || matches(s, SignedFloat, UnSignedFloat)&& !floatOk(s)); ck(bad); return new C(f(c.name), map(c.ts,this::visitT)); }
    String parameterToName(Parameter p, boolean hasPat){ return switch(p.xp){ case null -> "_";
        case XPat.Name(var x)-> hasPat && !x.equals("_") ? meths.fresh.variable(owner,x): x;
        case XPat.Destruct _ -> meths.fresh.variable(owner,"div"); }; }
    List<IM> visitMs(List<PM> ms){ return range(ms.size()).mapToObj(i -> visitM(ms.get(i), i)).toList();}
    ISig visitMSig(PM mm,int idx){ var s=mm.sig; var ts= map(s.ps,p -> visitT(p.t)); if(mm.implicit) ts = push(ts,unknown);
      return new ISig(s.rc, s.m == null ? null : s.m.arity(mm.arity()), s.bs, ts, visitT(s.t), null, mm.body == null, idx);} IM visitM(PM m,int idx){ var sig= visitMSig(m, idx);
      if(m.body == null) return new IM(sig); var body=m.body; var original=m.sig.ps;
      var hasPat= any(original,p -> p.xp instanceof XPat.Destruct);
      var ps= map(original,p -> parameterToName(p, hasPat));
      var xpats= flat(zip(ps, original,(x,p)-> xpat(p.xp,x)), s -> s); if(m.implicit){
        var p= meths.fresh.variable(owner,"impl"); var inner= hasPat ? meths.fresh.variable(owner,"impl"): p; ps = push(ps,p);
        if(hasPat) xpats = push(xpats,new XE(inner,new PE.X(p))); implicits.add(inner);} if(hasPat){
        var pps= map(xpats, xe -> new Parameter(new XPat.Name(xe.x), unknown));
        var fl=new PE.Lit(null, list(new PM(new PSig(null,null,null,pps, unknown), body, false)));
        body = new PE.Call(new PE.Typed(imm,new C(new TName("base.Destruct",0), list()), null), new MName("#", xpats.size()+1), null, null, push(map(xpats, XE::e), fl));
      } var e= visitE(body); if(m.implicit) implicits.removeLast(); return new IM(sig, ps, e); }
    Stream<XE>xpat(XPat xp,String lowered){ return switch (xp){ case null -> Stream.of(); case XPat.Destruct d -> zip(d.extract,d.names().toList(), (e,x)-> {
        PE res=new PE.X(lowered); for(var m : e) res = new PE.Call(res,new MName(m.s,0), null, null, list()); return new XE(x,res); }).stream();
      case XPat.Name(var x)-> x.equals(lowered)? Stream.of(): Stream.of(new XE(x,new PE.X(lowered))); };}
    Literal liftLiteral(RC rc,List<C> impl, PE.Lit l){ var ms= visitMs(l.ms);
      return new Literal(rc, meths.fresh.type(owner,0), list(), impl,or(l.self,"_"), ms,true);}
    Literal addDeclaration(TName name, RC rc, Declaration d, boolean top){ var self= or(d.l.self,top ?"this": "_");
      var bs=d.bs; var cs= map(d.cs,this::visitC);
      ck(duplicates(bs,map(cs,Frontend::normC)));
      var l=new Literal(rc,name, bs, cs,self, visitMs(d.l.ms), false); decs.add(l); return l;
    } PE.Call desugarCPat(PE.Call c){ var fresh=new PE.X(meths.fresh.variable(owner,"eqS")); var res= replaceAtom(c.es.get(1), fresh);
      var sig=new PSig(null,null,null, list(new Parameter(c.pat, unknown), new Parameter(new XPat.Name(fresh.name), unknown)), unknown);
      var par2=new PE.Lit(null, list(new PM(sig, res, false)));
      return new PE.Call(c.e,c.name,c.targs, null, list(c.es.get(0), par2)); } PE replaceAtom(PE par, PE atom){
      if (!(par instanceof PE.Call c)) return atom; return new PE.Call(replaceAtom(c.e, atom), c.name,c.targs,c.pat,c.es);} }
  static boolean duplicates(List<B> bs,List<C> cs){ var ts= map(cs,c -> new RCC(imm,c));
    return range(ts.size()).anyMatch(j -> range(j).anyMatch(i -> TypeSystem.shapeSub(bs, ts.get(i), ts.get(j)) && TypeSystem.shapeSub(bs, ts.get(j), ts.get(i))));
  } static final class Methods{
    final Pkg p; final Map<TName,Literal> other; final Fresh fresh; final HashMap<TName,Literal> cache=new HashMap<>();
    final HashMap<IE,Object> memo=new HashMap<>();
    Methods(Pkg p, Map<TName,Literal> other){ this.p=p; this.other= other; fresh=new Fresh(p);}
    List<Literal> headers(List<Literal> iDecs){ var rem=new LinkedHashMap<TName,Literal>();
      iDecs.forEach(d -> rem.put(d.name,d)); var acc=new ArrayList<Literal>(); while (!rem.isEmpty()){
        var layer= filter(rem.values(), d -> !any(d.cs,c -> c.name.pkg().equals(p.name)&& rem.containsKey(c.name)));
        ck(layer.isEmpty()); for(var d : layer){ rem.remove(d.name); var e= expand(d,false); if(d.self.equals("this")) acc.add(e);
          register(e);} } return acc;} List<C> fetchCs(C c){ var d= from(c.name); if(d == null)return list();
      return d.cs.stream().map(ci -> new C(ci.name, renameIT(ci.ts,B.xs(d.bs), c.ts))).distinct().toList();}
    List<ISig> fetchSigs(Literal child,C c, Literal d,List<String> scope){ return map(d.ms,m -> alphaSig(m,d,c, child, scope)); }
    ISig alphaSig(IM m, Literal d,C c, Literal child,List<String> scope){ var s=m.sig; var fullXs=new ArrayList<>(B.xs(d.bs));
      var fullTs=new ArrayList<>(c.ts); var newBs=new ArrayList<B>(); for(var b : s.bs){ var x=b.x;
        if (fresh.available(child.name,x, scope)){ newBs.add(b); continue;} fullXs.add(x);
        var newX=new X(fresh.generic(child.name,x, push(B.xs(s.bs), scope))); fullTs.add(newX); newBs.add(new B(newX.name,b.rcs)); }
      return s.subst(newBs, fullXs, fullTs);}
    Literal from(TName name){ return Frontend.from(name, cache::get, other);} Literal expand(Literal d, boolean setInfHead){
      var implied= flat(d.cs,c -> fetchCs(c).stream());
      var allCs= ToCore.distinct(d.bs, push(d.cs, implied.stream().sorted(Comparator.comparing(Print::of)).toList()));
      var allSig= flat(filter(d.cs,c -> !implied.contains(c)), c -> fetchSigs(d,c, from(c.name), list()).stream());
      var res=d.header(allCs, pair(names(d.ms,new ArrayList<>(allSig)), new ArrayList<>(allSig), d), setInfHead);
      magic(res, allCs); return res;} Literal implement(Literal d,C c,List<B> scope){ var dd= from(c.name);
      List<ISig> allSig= dd == null ? list(): fetchSigs(d,c, dd,B.xs(scope));
      return d.header(push(c, fetchCs(c)), pair(names(d.ms,new ArrayList<>(allSig)), new ArrayList<>(allSig), d), true);}
    void magic(Literal d,List<C> allCs){ ck(allCs.stream().filter(c -> c.name.equals(widen)).count()>1);
      if(any(allCs,c -> c.name.equals(baseId))){ var ms=d.ms;
        ck(ms.size()!=1 || !ms.get(0).sig.m.equals(new MName("#",1))); var s= ms.get(0).sig;
        ck(!(ms.get(0).e != null || s.abs || has(from(s.origin).cs, baseId))); }
      if (!any(allCs,c -> c.name.equals(sealed))) return;
      ck(any(allCs,c -> !c.name.pkg().equals(d.name.pkg()) && has(from(c.name).cs, sealed))); } void register(Literal d){
      var ms= map(d.ms,m -> m.signature(ToCore.sig(m.sig,m.sig)));
      cache.put(d.name,new Literal(or(d.rc, imm), d.name,d.bs,map(d.cs,Frontend::normC), d.self, ms,d.anonymous)); }
    List<IM> names(List<IM> ms, ArrayList<ISig> ss){ ss.removeIf(s -> any(ms,m -> Objects.equals(m.sig.m,s.m)));
      var named= filter(ms,m -> m.sig.m != null); return push(named, ms.stream().filter(m -> m.sig.m == null).map(m -> name(m, ss)).toList()); } IM name(IM m, ArrayList<ISig> ss){
      var arity=m.sig.ts.size(); for(var abs : list(true,false)){
        var match= filter(ss,s -> s.m.arity ==arity && (s.abs || !abs)); ss.removeAll(match);
        var count= match.stream().map(s -> s.m).distinct().count(); ck(count >1); if(count ==1){ var s=m.sig;
          return m.signature(new ISig(s.rc, match.get(0).m,s.bs,s.ts,s.ret,s.origin,s.abs,s.idx)); }} throw new Fail();}
    List<IM> pair(List<IM> ms, ArrayList<ISig> ss, Literal origin){ var res=new ArrayList<IM>(); for(var m : ms){
        var name=m.sig.m; var rc=m.sig.rc;
        var taken= filter(ss,s -> s.m.equals(name)&&(rc == null || rc == s.rc)); ss.removeAll(taken);
        var match= group(taken,s -> s.rc);
        if(rc == null && match.size()>1 && noH(or(origin.rc, or(origin.t.explicitRC(), imm))).readOnly()){
          var dead= match.remove(mut); if(dead != null) ss.addAll(dead);} var first=true;
        for(var matches : match.isEmpty()? list(List.<ISig>of()) : match.values()){
          var mi= first ? m : copyM(fresh,m, origin.name, origin.name); first = false; res.add(pair(matches, mi, origin)); }}
      group(ss,s -> new Key(s.rc, s.m)).values().forEach(v -> res.add(pair(v, null, origin)));
      return res;}
    IM pair(List<ISig> ss, IM om, Literal origin){ if (om == null && ss.size()==1)return new IM(ss.get(0));
      var s= om == null ? new ISig(null,null,null,qMarks(ss.get(0).m.arity), unknown,null,false,0): om.sig;
      if(ss.isEmpty()){ ck(any(s.ts,t -> t == unknown)|| s.ret == unknown);
        return om.signature(new ISig(or(s.rc, imm), s.m, or(s.bs,list()), s.ts,s.ret, origin.name, om.e == null, s.idx)); }
      var bs= or(s.bs, ss.get(0).bs); var rcss= ss.stream().map(e -> map(e.bs,B::rcs)).distinct().toList();
      ck(rcss.size()!=1 || !rcss.get(0).equals(map(bs,B::rcs)));
      var ssAligned= align(ss, bs); var first= ssAligned.get(0);
      var ts= range(s.ts.size()).mapToObj(i -> s.ts.get(i) == unknown ? agreement(origin, ssAligned,e -> e.ts.get(i)): s.ts.get(i)).toList();
      var res=s.ret == unknown ? agreement(origin, ssAligned, ISig::ret): s.ret;
      var impl= om != null ? List.<TName>of(): ssAligned.stream().filter(e -> !e.abs && !overridden(e, origin)).map(e -> e.origin).distinct().toList(); ck(impl.size()>1);
      var sig=new ISig(or(s.rc, first.rc), first.m, bs, ts,res, impl.size()==1 ? impl.get(0): origin.name, om == null ? impl.isEmpty(): om.e == null, s.idx);
      return om == null ? new IM(sig): om.signature(sig); } boolean overridden(ISig s, Literal lit){ var sup=s.origin; return lit.cs.stream()
        .flatMap(c -> Stream.concat(Stream.of(c.name), from(c.name).cs.stream().map(C::name))).anyMatch(t -> { var d= from(t);
          return !t.equals(sup)&& has(d.cs, sup)&& d.ms.stream().map(IM::sig).anyMatch(o -> o.origin.equals(d.name)&& o.m.equals(s.m)&& o.rc == s.rc);
        }); } IT agreement(Literal lit,List<ISig> ss, Function<ISig,IT> f){ var res= ss.stream().map(f).distinct().toList();
      var bs= push(lit.bs, ss.get(0).bs); var first= fill(res.get(0));
      ck(!all(res,t -> TypeSystem.equivalent(bs, first, fill(t)))); return res.get(0);}
    List<ISig> align(List<ISig> ss,List<B> bs){ return map(ss,s -> s.subst(bs,B.xs(s.bs), vars(bs))); }
    List<Literal> steps(List<Literal> tops){
      return map(tops,l -> { var di= cache.get(l.name); return di.header(di.cs, zip(l.ms, di.ms,(m,mCore)-> body(di,mCore,m)), false); }); }
    IM body(Literal di, IM mCore, IM m){
      if(m.e == null) return mCore; var e=m.e; var xs=m.xs; var ei= meet(e,mCore.sig.ret); var g=new IGamma();
      for(int i=0;i < xs.size(); i++) g.declare(xs.get(i), mCore.sig.ts.get(i));
      g.declare(di.self, di.self(mCore.sig.rc)); var bs= push(di.bs,m.sig.bs);
      ei = solve(bs,g, ei); return new IM(mCore.sig, xs, new ToCore(bs,this).core(ei,e)); } IE meet(IE e, IT t){
      if(e instanceof Type tt)return nextT(tt); if(e instanceof Literal l && l.t.isTV()) return e;e = ascribe(e,t,false);
      return e.withT(meet(e.t(), t)); } IT between(RCC x1, RCC x2){ var s1= below(x1,x2); if(s1 != null)return s1.isTV() || !x2.isTV()? s1 : x2;
      return below(x2,x1)== null ? x1 : between(x2,x1);} IT below(RCC sub, RCC sup){ var d= from(sub.c.name); if(d == null)return null; var ps= filter(d.cs,c -> c.name.equals(sup.c.name)); if(ps.isEmpty()) return null;
      var refined= meet(map(ps,c -> refine(B.xs(d.bs), new RCC(null,c), sup))); return sub.with(meetCap(sub.rc, sup.rc), meet(sub.c.ts, refined)); }
    IT meet(IT t1, IT t2){ if(t2.undecided()) return t1 == unknown ? t2 : t1;if(t1.undecided() || t1.equals(t2)) return t2;
      if(t1 instanceof ReadImmX(var x1)&& x1.equals(t2)) return t1;if(t2 instanceof ReadImmX(var x2)&& x2.equals(t1)) return t2;
      if(t1 instanceof RCC x1 && t2 instanceof RCC x2){ if (!x1.c.name.equals(x2.c.name)) return between(x1,x2);
        return x1.with(meetCap(x1.rc,x2.rc), meet(x1.c.ts,x2.c.ts)); }
      if (!(t1 instanceof RCX x1 && t2 instanceof RCX(var rc2,var x2)) || !x1.x.equals(x2)) return t1;
      return x1.withRC(meetCap(x1.rc, rc2)); } static RC meetCap(RC a, RC b){
      if(a == null)return b;if(b == null)return a; var x=noH(a); var y=noH(b);
      if(x == y || y == iso || y == read && x != iso)return x;if(x == iso || x == read)return y;
      return imm;} static RC noH(RC a){ return a == readH ? read : a == mutH ? mut : a;}
    IT join(IT t1, IT t2){ if(t2 == unknown)return t1;if(t1 == unknown || t1.equals(t2)) return t2;
      var cands= push(candidates(t1), candidates(t2)); for(var top : cands){ var res= aboveAll(top,cands); if(res != null)return res;}
      var common= common(cands); return common == null ? new Amb(cands): aboveAll(common,cands);}
    IT common(List<IT> cands){ if (!all(cands,c -> c instanceof RCC)) return null;
      var heads=cands.stream().map(c -> new ArrayList<>(superHeads((RCC)c))).reduce((a,b)-> { a.retainAll(b); return a; }).get();
      var minimal= filter(heads,h -> !any(heads,h2 -> !h2.equals(h)&& isSuper(h,h2)));
      return minimal.size()==1 ? supertypes((RCC)cands.get(0), minimal.get(0)).get(0): null;}
    List<TName> superHeads(RCC t){ var d= from(t.c.name); return d == null ? list(): map(d.cs,C::name);}
    static List<IT> candidates(IT t){ return t instanceof Amb(var cs)? cs : list(t);}
    IT aboveAll(IT top,List<IT> cands){ IT res= top; for(var c : cands){ var up= liftTo(c, top); if(up == null)return null; res = joinShape(res, up);} return res;}
    IT liftTo(IT c, IT top){ if(c instanceof RCC rc && top instanceof RCC rt){ if(rc.c.name.equals(rt.c.name)) return c;
        var up= supertypes(rc, rt.c.name); return up.isEmpty()? null : up.get(0); } return variable(c)!= null && variable(c).equals(variable(top)) ? c : null;}
    IT joinShape(IT a, IT b){ if(a instanceof RCC x1 && b instanceof RCC x2)return x1.with(joinCap(x1.rc,x2.rc), meet(x1.c.ts,x2.c.ts));
      if(a instanceof RCX x1 && b instanceof RCX x2)return x1.withRC(joinCap(x1.rc,x2.rc)); return meet(a,b);}
    static RC joinCap(RC a, RC b){ if(a == null)return b;if(b == null)return a; var x=noH(a); var y=noH(b);
      return x == y || y == iso ? x : x == iso ? y : read;}
    List<IT> join(List<List<IT>> tss){ return tss.stream().reduce((a,b)-> zip(a,b,this::join)).get();}
    List<IT> meet(List<IT> t1,List<IT> t2){ return zip(t1,t2,this::meet);}
    List<IT> meet(List<List<IT>> tss){ return tss.stream().reduce(this::meet).get(); } IE solve(List<B> bs, IGamma g, IE e){
      if(g.snap().equals(memo.get(e))) return e; while(true){ var s=g.snap(); var oe= next(bs,g,e);
        if (oe.equals(e) && s.equals(g.snap())){ memo.put(e,s); return e;} e = oe;} }
    List<IE> solve(List<B> bs, IGamma g,List<IE> es){ return map(es, ei -> solve(bs,g, ei)); }
    List<IE> expectArgs(List<IE> es, MSigL m,List<IT> targs){ return zip(es,m.ps0,(e,p)-> meet(e,m.inst(p,targs))); }
    IE next(List<B> bs, IGamma g, IE e){ return switch(e){ case IE.X x -> { ck(g.escapes(x.name));
          var t1=g.adapted(x.name); var t2=x.t;if(t1.equals(t2)){ yield x;} if (!t2.undecided()) updateG(g,x.name,t2);
          yield x.withT(meet(t1,t2)); } case Literal l -> nextL(bs,g,l); case Call c when c.written || c.rc != null -> nextC(bs,g,c); case Call c -> {
          var ee= solve(bs,g,c.e); var es= solve(bs,g,c.es);
          var m= ee.t() instanceof RCC rcc ? signature(rcc,c.name,null): null; if(m == null){ yield c.children(ee, es);}
          var ts=qMarks(m.methBs.size());
          yield new Call(ee,c.name,m.rc, ts, expectArgs(es,m, ts), false).withT(meet(c.t,m.inst(m.ret0, ts))); }
        case Type c -> nextT(c); }; } IT preferred(RCC type){ var d= from(type.c.name);
      var c=find(d.cs, ci -> ci.name.equals(widen)); if(c == null) return type;
      var wid= rename(c.ts.get(0), B.xs(d.bs), type.c.ts); if (!(wid instanceof RCC(_, var widC))) return type;
      return new RCC(type.rc, widC);} IM lookup(RCC rcc,MName name, RC favorite){
      var d= from(rcc.c.name); if(d == null)return null; var ms= filter(d.ms,m -> m.sig.m.equals(name));
      Function<RC,IM> one= rc -> find(ms,m -> m.sig.rc == rc);
      var rc=rcc.rc == null || rcc.rc == iso ? imm : noH(rcc.rc);
      var order= rc == read ? list(read, imm, mut): rc == mut ? list(mut, read, imm): list(imm, read, mut);
      return favorite != null ? one.apply(favorite): ms.size()==1 ? ms.get(0) : order.stream().map(one).filter(Objects::nonNull).findFirst().orElse(null);}
    MSigL signature(RCC rcc,MName name, RC favorite){ var d= from(rcc.c.name); var m= lookup(rcc,name, favorite);
      return m == null ? null : new MSigL(m.sig.rc, push(B.xs(d.bs), B.xs(m.sig.bs)), d.bs,rcc.c.ts,m.sig.bs,m.sig.ts,m.sig.ret); }
    static void updateG(IGamma g,String x, IT t2){ var t1=g.get(x); var t=t1.undecided()? t2
        : t1 instanceof RCC(var aRc,var aC)&& t2 instanceof RCC(var bRc,var bC)&& aC.name.equals(bC.name)? new RCC(aRc == null ? bRc : bRc == null ? aRc : lowerCap(aRc,bRc), aC)
        : t1 instanceof RCX a && t2 instanceof RCX(var bRc,var bX)&& a.x.equals(bX)? a.withRC(lowerCap(a.rc,bRc)): null;
      if(t != null) g.fs.get(g.at(x)).vars.put(x,t);} static RC lowerCap(RC a, RC b){ a = noH(a); b = noH(b);
      return a == b || b == read ? a : a == read ? b : iso;} IE nextT(Type t){ return t.t.undecided()? t.withT(preferred(t.type)): t;}
    IE nextC(List<B> bs, IGamma g, Call c){ var e= solve(bs,g,c.e);
      if (!(e.t() instanceof RCC rcc)|| signature(rcc,c.name,c.rc)== null) return c.children(e, solve(bs,g,c.es));
      var m= signature(rcc,c.name,c.rc); var nCls=m.clsArgs.size();
      var all0= inferArgs(c,m,c.es,false); var m0=m.arguments(normalize(bs,m.clsBs, all0.subList(0,nCls)));
      var es= solve(bs,g, expectArgs(c.es,m0, normalize(bs,m.methBs, all0.subList(nCls, all0.size()))));
      var all= inferArgs(c,m, es,true); var clsTs= normalize(bs,m.clsBs, all.subList(0,nCls));
      var targs= normalize(bs,m.methBs, all.subList(nCls, all.size())); e = meet(e,rcc.withTs(clsTs)); var m1=m.arguments(clsTs);
      return new Call(e,c.name,or(c.rc,m1.rc), targs, expectArgs(es,m1,targs), meet(c.t,m1.inst(m1.ret0,targs)),c.written);
    } List<IT> fromArgs(MSigL m,List<IE> es, boolean onlyLiterals){
      var is= range(es.size()).filter(i -> !onlyLiterals || es.get(i) instanceof Literal).boxed().toList();
      Function<Integer,List<IT>> ref=i -> refine(m.xs,m.ps0.get(i), es.get(i).t());
      var lower= map(filter(is,i -> !(m.ps0.get(i) instanceof RCC)), ref); var exact= map(filter(is,i -> m.ps0.get(i) instanceof RCC), ref);
      return meet(push(join(push(qMarks(m.xs.size()), lower)), exact)); }
    List<IT> inferArgs(Call c, MSigL m,List<IE> es, boolean useArgs){ var targs= MSigL.fixTargs(c.targs,m.methBs.size());
      var args= useArgs ? fromArgs(m, es,false): qMarks(m.xs.size());
      var all= meet(List.of(push(m.clsArgs,targs), args, refine(m.xs,m.ret0,c.t)));
      var written= push(m.clsArgs,c.written ? targs : qMarks(m.methBs.size())); var hard= fromArgs(m, es,true);
      var fixed= zip(written, hard,(w,h)-> decided(w)? w : h); return zip(fixed, all,(b,r)-> decided(b)? b : r);}
    static boolean decided(IT t){ return t.isTV() && !(t instanceof RCC(var rc, _) && rc == null);} RCC self(Literal l){
      return l.anonymous && l.rc == null ? null : l.self(l.rc); }
    IE nextL(List<B> bs, IGamma g, Literal l){ var selfPrecise=self(l); if (!l.expanded){ var cs0=l.cs;
        var selfSuper= cs0.size()!=1 || selfPrecise == null ? selfPrecise : new RCC(selfPrecise.rc, cs0.get(0));
        l = l.withT(l.anonymous ? or(selfSuper,l.t): selfPrecise); if (!(l.t instanceof RCC(_, var c))) return l;
        l = l.anonymous && !c.name.equals(l.name)? implement(l,c, bs): expand(l,true);}
      if (!(l.t instanceof RCC rcc)) return l; var res=new ArrayList<IM>(); var ts=rcc.c.ts; for(var mi : l.ms){
        var rcci= bound(rcc, ts); var next= mi.e == null ? header(rcci, mi): nextM(bs,g,l,selfPrecise,rcci, mi);
        ts = meet(ts,next.ts); res.add(next.m);}
      if(res.equals(l.ms) && ts.equals(rcc.c.ts)) return commit(g, bs,l,rcc); var t= bound(rcc, ts);
      return commit(g, bs,l.header(l.cs,res,true).withT(t), t);} IE commit(IGamma g,List<B> bs, Literal l, RCC rcc){ var name=l.name;
      if (!rcc.isTV() || !all(l.ms,m -> m.sig.ret.isTV() && all(m.sig.ts, IT::isTV)) || cache.containsKey(name)) return l;
      var localBs= cat(ftvMs(g,l.ms), ftvCs(l.cs), rcc.ftv()).distinct().map(x -> B.get(bs,x)).toList(); var newName=name.arity(localBs.size());
      var ms= map(l.ms, mi -> !mi.sig.origin.equals(name)? mi : mi.signature(mi.sig.origin(newName)));
      var orc=noH(or(l.rc,rcc.rc)); var orcc=new RCC(orc,rcc.c);
      if(all(l.ms,m -> m.e == null) && l.expanded && from(rcc.c.name)!= null)return new Type(orcc, preferred(orcc));
      var selfInferred=rcc.c.name.equals(l.name);
      var cs= ToCore.distinct(localBs,selfInferred ? fetchCs(rcc.c): push(rcc.c, fetchCs(rcc.c))); magic(l, cs);
      l = new Literal(orc,newName, localBs, cs,l.self, ms,rcc,l.anonymous,l.expanded);
      if(selfInferred) l = l.withT(self(l)); register(l); return l;} record TSM(List<IT> ts, IM m){} TSM header(RCC rcc, IM m){
      var sig=m.sig; var omh= lookup(rcc, sig.m, sig.rc); if (omh == null) return new TSM(rcc.c.ts,m);
      var rcc0= bound(rcc, refineHeader(rcc, sig,omh.sig));
      return new TSM(erase(rcc0.c.ts,B.xs(sig.bs)), m.signature(signature(rcc0, sig))); }
    TSM nextM(List<B> bs, IGamma g, Literal l, RCC selfPrecise, RCC rcc, IM m){ var litBs=l.anonymous ? bs : l.bs;
      g.fs.add(new IGamma.Frame(m.sig.rc, litBs,new HashMap<>()));
      g.declare(l.self,selfPrecise == null ? unknown : new RCC(selfPrecise.rc == null ? null : selfPrecise.rc.isoToMut(), selfPrecise.c));
      g.fs.add(new IGamma.Frame(m.sig.rc, litBs,new HashMap<>()));
      for(int i=0;i < m.xs.size(); i++) g.declare(m.xs.get(i), m.sig.ts.get(i));
      var e= solve(push(litBs,m.sig.bs), g, meet(m.e, m.sig.ret));
      var args= zip(m.xs,m.sig.ts,(x,t)-> x.equals("_") ? t : meet(t,g.get(x))); g.fs.removeLast();
      g.fs.removeLast(); var h= header(rcc,m.signature(m.sig.types(args, meet(m.sig.ret,e.t())))); var sig=h.m.sig;
      return new TSM(h.ts, new IM(sig,m.xs, meet(e, sig.ret))); }
    List<IT> refineHeader(RCC rcc, ISig improvedSig, ISig imh){ var Xs=B.xs(from(rcc.c.name).bs);
      var byArg= zip(imh.ts, improvedSig.ts,(t,it)-> refine(Xs,t,it)); var fromBody= meet(push(byArg, refine(Xs,imh.ret, improvedSig.ret)));
      return zip(rcc.c.ts, fromBody,this::keep);} IT keep(IT decided, IT fromBody){
      var decidedIso= decided instanceof RCX(var aRc, _) && aRc == iso;
      if(variable(decided)!= null && variable(decided).equals(variable(fromBody)) && !decidedIso)return decided;
      if (!(decided instanceof RCC(var aRc,var aC)&& fromBody instanceof RCC b)) return meet(decided, fromBody);
      if (!aC.name.equals(b.c.name)){ var asDecided= supertypes(b,aC.name);
        return asDecided.isEmpty()? decided : keep(decided, asDecided.get(0)); }
      return b.with(or(aRc,b.rc), zip(aC.ts,b.c.ts,this::keep)); } ISig signature(RCC rcc, ISig improvedSig){
      var h= signature(rcc, improvedSig.m, improvedSig.rc); var xs= vars(improvedSig.bs);
      return improvedSig.types(map(h.ps0,p -> h.inst(p, xs)), h.inst(h.ret0, xs)); }
    List<IT> erase(List<IT> ts,List<String> methBs){ if (methBs.isEmpty()) return ts;
      return map(ts,t -> t instanceof RCC rcc ? bound(rcc, erase(rcc.c.ts, methBs)): methBs.contains(variable(t))? unknown : t);
    } List<IT> refine(List<String> xs, IT t, IT t1){ if(t1.undecided()) return qMarks(xs.size()); return switch(t){
        case X x -> { var n= xs.indexOf(x.name); yield range(xs.size()).<IT>mapToObj(i -> i == n ? t1 : unknown).toList();}
        case RCX(_, var x)-> refine(xs,x, switch(t1){ case RCX(_, var x1)-> x1;
          case ReadImmX(var x1)-> x1; case RCC(_, var c)-> new RCC(null,c); default -> t1; });
        case ReadImmX(var x)-> refine(xs,x,t1 instanceof ReadImmX(var x1)? x1 : t1); case RCC rcc -> propagate(xs,rcc,t1);
        case U _, Amb _ -> qMarks(xs.size()); }; } boolean isSuper(TName a,TName b){ var d= from(b); return d != null && has(d.cs,a);}
    List<RCC> supertypes(RCC src,TName target){ var d= from(src.c.name); if(d == null)return list();
      return d.cs.stream().filter(sc -> sc.name.equals(target)).distinct()
        .map(ci -> (RCC)rename(new RCC(src.rc, ci), B.xs(d.bs), src.c.ts)).toList(); } List<IT> propagate(List<String> xs, RCC r, IT t1){
      if (!(t1 instanceof RCC cc)) return qMarks(xs.size()); var c=r.c;if (!cc.c.name.equals(c.name)){ var supOk= supertypes(cc,c.name);
        if (!supOk.isEmpty()) return propagate(xs,r, supOk.get(0)); var subOk= supertypes(r, cc.c.name);
        if (!subOk.isEmpty()) return propagate(xs, subOk.get(0), t1); return qMarks(xs.size()); }
      var res= zip(c.ts, cc.c.ts,(t,ti)-> t instanceof RCC rr && !(ti instanceof RCC ci && ci.c.name.equals(rr.c.name)) ? qMarks(xs.size()) : refine(xs,t, ti));
      return res.isEmpty()? qMarks(xs.size()) : meet(res);} IE ascribe(IE arg, IT expected, boolean receiver){ if (!(expected instanceof RCC exp)) return arg;
      return switch(arg){ case Call c -> c.children(ascribe(c.e, expected,true), c.es);
        case Literal l when l.expanded || !l.anonymous || !l.cs.isEmpty() || !l.t.undecided()-> arg;
        case Literal l when !receiver || implementable(exp.c.name)-> l.withT(new RCC(exp.rc,new C(exp.c.name,qMarks(exp.c.ts.size()))));
        case Literal l -> { var res=new Literal(imm,l.name,l.bs,l.cs,l.self,l.ms,true);
          yield res.withT(self(res)); } default -> arg; }; } boolean implementable(TName head){ var d= from(head);
      if(d == null)return false; var foreignForbidden=!head.pkg().equals(p.name)&& (!head.visible() || has(d.cs, sealed));
      return !foreignForbidden && TypeSystem.hasInstance(d);} static IT normalize(IT t, Set<RC> allowed){
      if (allowed.size()==1)return t.withRC(allowed.iterator().next()); if (!(t instanceof RCC(var rc,var c))) return t;
      if (!(rc == null || rc == iso && !allowed.contains(iso))) return t;
      return new RCC(allowed.contains(imm)? null : read,c);}
    static List<IT> normalize(List<B> scope,List<B> bs,List<IT> ts){
      return zip(ts, bs,(ti,bi)-> variable(ti)== null || B.get(scope,variable(ti)).rcs.equals(bi.rcs)? normalize(ti, bi.rcs): ti);}
    static String variable(IT t){ return switch(t){ case X x -> x.name; case RCX(_, var x)-> x.name;
      case ReadImmX(var x)-> x.name; default -> null; };} RCC bound(RCC rcc,List<IT> ts){
      var d= from(rcc.c.name); return d == null ? rcc.withTs(ts): rcc.withTs(zip(ts,d.bs,(ti,bi)-> normalize(ti, bi.rcs))); }
  }
  record ToCore(List<B> ctx, Methods meths){ IE core(IE exp, IE orig){ return switch(exp){ case IE.X(var name, _) -> new IE.X(name);
      case Type(var type, _) -> new Type((RCC)norm(type)); case Literal le -> literal(le,(Literal)orig); case Call e -> { var o=(Call)orig; var ts=o.targs.isEmpty()? e.targs : o.targs;
        yield new Call(core(e.e,o.e), e.name,or(e.rc, imm), range(ts.size()).<IT>mapToObj(i -> targ(e, ts.get(i), i)).toList(), zip(e.es,o.es,this::core), false);
      }};} IT targ(Call e, IT t,int i){ if (!(t == unknown)) return norm(fillVoid(t));
      var m=e.e.t() instanceof RCC rcc ? meths.lookup(rcc,e.name,e.rc): null; var rcs= m == null ? rcs(imm): m.sig.bs.get(i).rcs;
      return voidT(rcs.contains(imm)? imm : rcs.iterator().next()); } static IT voidT(RC rc){ return new RCC(rc,new C(baseVoid,list())); }
    static IT fillVoid(IT t){ ck(t instanceof Amb); return t == unknown ? voidT(imm): t instanceof RCC rcc ? rcc.withTs(map(rcc.c.ts, ToCore::fillVoid)): t;}
    Literal literal(Literal e, Literal o){ ck(!(e.t instanceof RCC)&& !e.t.undecided()); var bs=e.bs;if(e.anonymous && bs.isEmpty()){ var g=new IGamma();
        bs = cat(ftvCs(e.cs), ftvMs(g,e.ms), ftvMs(g,o.ms)).distinct().map(x -> B.get(ctx,x)).toList(); } var name=e.name.arity(bs.size());
      var inner=e.anonymous ? with(bs): new ToCore(bs, meths);
      var ms=e.ms.stream().map(me -> inner.m(me, me.e == null ? me : o.ms.get(me.sig.idx)))
        .map(m -> !m.sig.origin.equals(e.name)? m : m.signature(m.sig.origin(name))).toList();
      var cs= map(distinct(inner.ctx,o.cs.isEmpty()? e.cs : push(o.cs,e.cs)),Frontend::normC);
      return new Literal(or(e.rc, imm), name, bs, cs,e.self, ms,e.anonymous);}
    static List<C> distinct(List<B> bs,List<C> cs){ var res=new ArrayList<C>();
      for(var c : cs){ if (!any(res,r -> TypeSystem.equivalent(bs, fill(new RCC(imm,r)), fill(new RCC(imm,c))))) res.add(c);}
      return res;} ToCore with(List<B> bs){ return new ToCore(push(ctx, bs).stream().distinct().toList(), meths);} IM m(IM e, IM o){ var s= sig(e.sig,o.sig);
      return new IM(s,e.xs,e.e == null ? null : with(s.bs).core(e.e,o.e));}
    static ISig sig(ISig inf, ISig usr){ var ts= zip(usr.ts, inf.ts,(u,i)-> u == unknown ? i : u);
      return new ISig(or(usr.rc, or(inf.rc, imm)), required(or(usr.m, inf.m)), or(usr.bs, or(inf.bs,list())),
        map(ts,Frontend::norm), norm(usr.ret == unknown ? inf.ret : usr.ret), required(or(usr.origin, inf.origin)), usr.abs, usr.idx);} }
  record Gamma(Gamma tail,String name, IT current){ static final Gamma empty=new Gamma(null,null,null);
    Gamma add(String name, IT t){ return new Gamma(this,name,t);}
    Gamma map(UnaryOperator<IT> f){ return this == empty ? this : new Gamma(tail.map(f), name,current == null ? null : f.apply(current)); }
    IT bind(String x){ return this == empty ? null : name.equals(x)? current : tail.bind(x);}
    Gamma filterFTV(Literal l, boolean captureFree){
      if(this == empty)return this; var rest= tail.filterFTV(l, captureFree);
      var drop= captureFree || current != null && !current.ftv().allMatch(B.xs(l.bs)::contains);
      return new Gamma(rest,name, drop ? null : current);} }
  record MType(RC rc,List<IT> ts, IT t){} enum Mode{
    useRead(iso, readH, mutH, readH), flexy(iso, imm, mutH, readH), hyg(mutH, readH, mutH, readH), strong(iso, imm, iso, imm); final RC m,r, mh, rh;
    Mode(RC m, RC r, RC mh, RC rh){ this.m=m; this.r=r; this.mh= mh; this.rh= rh;}
    RC of(RC rc){ return switch(rc){ case mut -> m; case read -> r; case mutH -> mh; case readH -> rh; default -> rc; }; }}
  record TypeSystem(Function<TName,Literal> decs){ static void allOk(List<Literal> tops, Map<TName,Literal> other){ var map=new HashMap<TName,Literal>();
      tops.forEach(t -> collect(t,map)); var ts=new TypeSystem(n -> from(n,map::get, other)); tops.forEach(l -> ts.litOk(Gamma.empty,l)); }
    static void collect(IE e, HashMap<TName,Literal> map){ if(e instanceof Literal l) map.put(l.name,l); e.children().forEach(c -> collect(c,map)); }
    boolean kindOf(List<B> bs, IT t, Set<RC> allowed){ if (!allowed.containsAll(caps(bs,t))) return false;
      if (!(t instanceof RCC(_, var c))) return true; var params= decs.apply(c.name).bs;
      return all(zip(c.ts, params,(ti,p)-> kindOf(bs, ti,p.rcs)), v -> v);}
    void kind(List<B> bs, IT t, Set<RC> allowed){ ck(!kindOf(bs,t, allowed)); }
    static Set<RC> caps(List<B> bs, IT t){ return switch(t){ case RCC(var rc, _) -> rcs(rc);
      case RCX(var rc, _) -> rcs(rc); case X(var x)-> B.get(bs,x).rcs; case U _, Amb _ -> throw new Fail(); case ReadImmX(var x)-> {
        var rcs= caps(bs,x);
        yield isoImm.containsAll(rcs)? rcs(imm): rcs(mut, mutH, read, readH).containsAll(rcs)? rcs(read): rcs(read, imm);
      }};} Gamma vpaOf(Gamma g, Literal l, IM m){
      return g.map(t -> { if(m.sig.rc == imm || kindOf(l.bs,t, isoImm)) return t.withRC(imm); if(m.sig.rc == read){
          if(t.explicitRC()== mut || t.explicitRC()== read)return t.withRC(read);
          if(t instanceof X || t instanceof ReadImmX)return t.readImm();}
        return kindOf(l.bs,t, rcs(imm, mut, read)) ? t : t.readImm(); }); } Gamma discard(Gamma g, Literal l){
      return g.map(t -> { var drop=!kindOf(l.bs,t, allRC)|| !kindOf(l.bs,t,noHyg)|| l.rc.isoImm() && !kindOf(l.bs,t, isoImm);
        return drop ? null : t; }); } boolean isSub(List<B> bs, IT t1, IT t2){ return t1.equals(t2)
        || t2 instanceof ReadImmX(var x2)&& t1 instanceof X x && x2.name.equals(x.name)&& kindOf(bs,x,noHyg)
        || shapeSub(bs,t1,t2)
        || t1 instanceof RCC(var rc1,var c1)&& any(decs.apply(c1.name).cs, ci -> isSub(bs, rename(new RCC(rc1, ci), B.xs(decs.apply(c1.name).bs), c1.ts), t2));
    } List<IT> typeOf(List<B> bs, Gamma g, IE e,List<IT> rs){ return switch(e){ case IE.X x -> {
        var t=g.bind(x.name); ck(t == null); yield reqs(bs,t, rs,false);} case Type t -> {
        kind(bs,t.type,allRC); var ll= decs.apply(t.type.c.name); ck(!hasInstance(ll)); var rc=t.type.rc;
        var getIso=(rc.readOnly() && !abstractMut(ll)) || rc == mut || rc == mutH; var l= ll.withRC(getIso ? iso : rc);
        l.ms.forEach(m -> ck(m.sig.abs && callable(l.rc,m.sig.rc))); yield reqs(bs,getIso ? t.type.withRC(iso): t.type, rs,true);}
      case Literal l -> literal(bs,g,l, rs); case Call c -> call(bs,g,c, rs); };}
    static boolean hasInstance(Literal l){ return l.self.equals("this") || has(l.cs, captureFree);}
    static long count(String x, IE e, boolean active){ var here=e instanceof IE.X v && v.name.equals(x)?1 :0;
      if(active && e instanceof Literal)return here; return here + e.children().mapToLong(c -> count(x,c, active)).sum();}
    static boolean abstractMut(Literal l){ return any(l.ms,m -> m.sig.abs && m.sig.rc == mut);}
    List<IT> reqs(List<B> bs, IT got,List<IT> rs, boolean rccOnly){ if(rs.isEmpty()) return list(got);
      ck(rccOnly && any(rs,r -> !(r instanceof RCC))); return map(rs,r -> isSub(bs, got,r)? got : null);}
    List<IT> literal(List<B> bs1, Gamma g, Literal _l,List<IT> rs){ var selfNamed= !_l.self.equals("_"); var cf= has(_l.cs, captureFree);
      var getIso= ((_l.rc.readOnly() && !abstractMut(_l)&& !selfNamed)|| _l.rc == mut)&& captureFree(_l.bs,g.filterFTV(_l, cf), _l);
      var l=getIso ? _l.withRC(iso): _l;
      ck(any(rs,r -> !(r instanceof RCC)));
      var thisType=l.self(l.rc); kind(bs1,thisType,allRC); litOk(discard(g.filterFTV(l, cf), l), l);
      ck(selfNamed && count(_l.self,_l,false)==0); ck(any(l.ms,m -> m.e != null && !hasInstance(l)&& !callable(l.rc,m.sig.rc)));
      l.ms.forEach(m -> ck(m.sig.abs && callable(l.rc,m.sig.rc))); return reqs(bs1,thisType, rs,false);}
    static boolean captureFree(List<B> bs, Gamma g, IE e){ if (!(e instanceof IE.X x)) return e.children().allMatch(c -> captureFree(bs,g,c));
      return g.bind(x.name)== null || all(caps(bs,g.bind(x.name)), RC::isoImm);}
    static boolean callable(RC litRC, RC recRc){ return recRc != mut || !litRC.readOnly(); } void litOk(Gamma g, Literal l){
      if(has(l.cs, baseId)){ var m=l.ms.get(0); var isId= switch(m.e){ case null -> true;
          case IE.X(var name, _) -> name.equals(m.xs.get(0));
          case Call c -> c.e instanceof IE.X(var recv, _) && recv.equals(m.xs.get(0)) && c.name.equals(new MName(".as",1))
            && m.sig.ts.get(0) instanceof RCC(_, var cc)&& has(decs.apply(cc.name).cs, baseContainer); default -> false; }; ck(!isId);}
      var delta=l.bs; for(var c : l.cs){ kind(delta,new RCC(imm,c),allRC); ck(!hasInstance(decs.apply(c.name))); } var sources=new ArrayList<ISig>();
      for(var parent : l.cs){ var parentDef= decs.apply(parent.name); for(var m : parentDef.ms){
          if (!m.sig.origin.equals(parentDef.name)) continue; var s=m.sig; var canonical= canonical(l,s.m,s.rc).bs;
          var mapXs=B.xs(push(s.bs,parentDef.bs)); var mapTs= push(vars(canonical), parent.ts);
          sources.add(s.subst(canonical,mapXs,mapTs));
        }} for(var m : l.ms){ if(m.sig.origin.equals(l.name)) sources.add(m.sig);}
      group(sources,s -> new Key(s.rc, s.m)).forEach((k,sigs)-> { var chosen= canonical(l,k.name,k.rc); var ctx= push(l.bs, chosen.bs); for(var s : sigs){
          for(int i=0;i < chosen.ts.size(); i++) ck(!sameCap(ctx, chosen.ts.get(i), s.ts.get(i)) || !isSub(ctx,s.ts.get(i), chosen.ts.get(i)));
          ck(!sameCap(ctx, chosen.ret,s.ret)|| !isSub(ctx, chosen.ret,s.ret)); } });
      var g1=g.add(l.self,l.self(l.rc.isoToMut())); for(var m : l.ms){ var g2=vpaOf(g1,l,m);
        var allBs= push(delta,m.sig.bs); m.sig.ts.forEach(t -> kind(allBs,t,allRC)); kind(allBs,m.sig.ret,allRC); if(m.e == null) continue;
        for(int i=0;i < m.xs.size(); i++) g2 = g2.add(m.xs.get(i), m.sig.ts.get(i)); ck(typeOf(allBs,g2,m.e, list(m.sig.ret)).get(0)== null);
        for(int i=0;i < m.xs.size(); i++){ var x=m.xs.get(i); if(kindOf(allBs,m.sig.ts.get(i), rcs(mut, read, mutH, readH, imm))) continue;
          ck(count(x,m.e, true)>0 && count(x,m.e, false)!=1);}
      }} static ISig canonical(Literal l,MName name, RC rc){ return find(l.ms,m -> m.sig.m.equals(name)&& m.sig.rc == rc).sig;}
    static boolean shapeSub(List<B> bs, IT t1, IT t2){
      if (!equivalent(bs,t1.withRC(mut), t2.withRC(mut))) return false; var rcs2= caps(bs,t2);
      return all(caps(bs,t1), r1 -> all(rcs2,r1::isSubType)); } static boolean sameCap(List<B> bs, IT a, IT b){
      return(a instanceof ReadImmX)== (b instanceof ReadImmX)&& a.explicitRC()== b.explicitRC() || equivalent(bs,a,b);}
    static boolean equivalent(List<B> bs, IT a, IT b){ if(a.equals(b)) return true;
      if (!(a instanceof RCC(var aRc,var aC)&& b instanceof RCC(var bRc,var bC))){
        if (!(a.withRC(imm) instanceof RCX(_, var x)) || !a.withRC(imm).equals(b.withRC(imm))) return false;
        return B.get(bs,x.name).rcs.size()==1 && caps(bs,a).equals(caps(bs,b)); }
      return aRc == bRc && aC.name.equals(bC.name)&& all(zip(aC.ts,bC.ts,(x,y)-> equivalent(bs,x,y)), v -> v);}
    List<IT> call(List<B> bs, Gamma g, Call c,List<IT> rs){
      if (!(typeOf(bs,g,c.e,list()).get(0) instanceof RCC rcc0)) throw new Fail(); var d= decs.apply(rcc0.c.name);
      var sig= required(find(d.ms,m -> m.sig.m.equals(c.name)&& m.sig.rc == c.rc)).sig;
      ck(sig.bs.size()!= c.targs.size()); for(int i=0;i < c.targs.size(); i++) kind(bs,c.targs.get(i), sig.bs.get(i).rcs);
      var xs=B.xs(push(d.bs, sig.bs)); var ts0= push(rcc0.c.ts,c.targs);
      var base=new MType(sig.rc, renameIT(sig.ts, xs, ts0), rename(sig.ret, xs, ts0));
      var app= filter(promotions(bs, base), m -> rcc0.rc.isSubType(m.rc)); ck(app.isEmpty());
      var possible= app; for(int i=0;i < c.es.size(); i++){ var ai=i;
        var reqs= app.stream().map(m -> m.ts.get(ai)).distinct().toList(); var got= typeOf(bs,g,c.es.get(i), reqs);
        ck(all(got, Objects::isNull)); possible = filter(possible,m -> got.get(reqs.indexOf(m.ts.get(ai))) != null);}
      ck(possible.isEmpty()); var candidates= possible;
      if(rs.isEmpty()) return list(best(bs, candidates)); return map(rs, req -> {
        var ok= filter(candidates,m -> isSub(bs,m.t, req)); return ok.isEmpty()? null : best(bs, ok); }); }
    IT best(List<B> bs,List<MType> ms){ var ts= map(ms,MType::t);
      return find(ts,a -> !any(ts,b -> !b.equals(a)&& isSub(bs,b,a)));}
    static RC lub(Set<RC> rcs){ return bound(rcs, RC::isSubType);} static RC glb(Set<RC> rcs){ return bound(rcs,(a,b)-> b.isSubType(a)); }
    static RC bound(Set<RC> rcs, BiPredicate<RC,RC> le){ var bs= Stream.of(RC.values()).filter(b -> all(rcs,x -> le.test(x,b))).toList();
      return find(bs,b -> all(bs,o -> le.test(b,o))); } static List<MType> promotions(List<B>d,MType m){
      return Stream.concat(Stream.of(m, apply(d,m, flexy,flexy,-1, flexy), apply(d,m,strong,strong,-1,strong), apply(d,m,useRead,useRead,-1, hyg), apply(d,m, hyg,flexy,-1, hyg)),
        range(m.ts.size()).mapToObj(i -> apply(d,m, flexy,flexy,i, hyg))).distinct().toList();}
    static MType apply(List<B>d,MType m, Mode rcM, Mode tsM,int at, Mode retM){
      return new MType(rcM.of(m.rc), range(m.ts.size()).mapToObj(j -> modeF(d,m.ts.get(j), j == at ? hyg : tsM, TypeSystem::glb)).toList(), modeF(d,m.t, retM, TypeSystem::lub)); }
    static IT modeF(List<B>d, IT t, Mode mode, Function<Set<RC>,RC> f){ return switch(t){ case RCC rcc -> rcc.withRC(mode.of(rcc.rc));
        case RCX rcx -> rcx.withRC(mode.of(rcx.rc)); case X x -> modeVar(d,x, rc -> rc, mode,f,t);
        case ReadImmX(var x)-> modeVar(d,x, RC::readImm, mode,f,t); case U _, Amb _ -> t; }; }
    static IT modeVar(List<B>d,X x, UnaryOperator<RC> inst, Mode mode, Function<Set<RC>,RC> f, IT original){
      var rcs= EnumSet.copyOf(map(B.get(d,x.name).rcs, inst)); if(all(rcs, rc -> mode.of(rc)== rc)) return original;
      return new RCX(f.apply(EnumSet.copyOf(map(rcs, mode::of))), x);} }}
