package fearlessParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import fearlessFullGrammar.*;
import files.Pos;
import message.FearlessErrFactory;
import message.FearlessException;
import metaParser.MetaParser;
import metaParser.Span;
import utils.Bug;

import static fearlessParser.TokenKind.*;
import static java.util.Optional.of;
import static java.util.Optional.empty;
import static metaParser.MetaParser.SplitMode.*;


public class Parser extends MetaParser<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>{
  Names names;
  Parser(Span base, Names names, List<Token> ts){
    super(base,ts); this.names= names;
  }
  void updateNames(Names names){ this.names = names; }
  @Override public Parser self(){ return this; }
  @Override public boolean skip(Token t){ return t.is(_SOF,_EOF); }
  @Override public Parser make(Span s, List<Token> tokens){
    return new Parser(s, names, tokens);
  }
  E parseE(){
    E e= parseAtom();
    while(!end()){ e = parsePost(e); }
    return e;
  }
  boolean hasPost(){ return peek(DotName,Op,UStrInterHash,UStrLine,SStrInterHash,SStrLine); }
  boolean isDec(){//Dec starts with D[Bs]: or D:
    return peekOrder(t->t.isTypeName(), t->t.is(_SquareGroup), t->t.is(Colon))
        || peekOrder(t->t.isTypeName(), t->t.is(Colon));
  }
  E parseAtom(){
    if(peek(LowercaseId)){ return parseX(); }
    if(peek(_RoundGroup)){ return parseGroup("expression in round parenthesis",Parser::parseRound); }
    if(peek(ColonColon)){ return parseImplicit(); }
    if(peek(UStrInterHash,UStrLine)){ return parseStrInter(false,empty()); }
    if(peek(SStrInterHash,SStrLine)){ return parseStrInter(true,empty()); }
    if(peek(_CurlyGroup)){ return parseGroup("object literal", p->p.parseLiteral(false,false)); }
    var rcSpan= peek().map(t->span(t).orElse(span()));
    Optional<RC> rc= parseOptRC();
    var invalid= rc.map(_rc->_rc==RC.mutH || _rc==RC.readH).orElse(false);
    if(invalid){ throw errFactory().disallowedReadHMutH(rcSpan.get(), rc.get()); }
    if(isDec()){ return new E.DeclarationLiteral(rc,parseDeclaration(false)); }
    if(!peek(Token.typeName)){ expect("expression",LowercaseId,UppercaseId,ORound,OCurly); }
    //the expect above is guaranteed to go in error, the list of tokens is cherry picked to produce
    //and intuitive error message
    return parseTypedLiteral(rc);
  }
  RC parseRC(){ return RC.valueOf(expect("reference capability",RCap).content()); }
  Optional<RC> parseOptRC(){ return peek(RCap)? of(parseRC()) : empty(); }
  E.TypedLiteral parseTypedLiteral(Optional<RC> rc){
    Pos pos= pos();
    var c= new T.RCC(rc, parseC());
    var isCurly= peek(_CurlyGroup);
    if(!isCurly){ return new E.TypedLiteral(c,empty(),pos); }
    return new E.TypedLiteral(c,of(parseGroup("typed literal",p->p.parseLiteral(false,true))),pos);
  }
  T.C parseC(){
    var c= parseTName();
    if(!peek(_SquareGroup)){ return new T.C(c, empty()); }
    List<T> ts= parseGroupSep("","generic types",Parser::parseT,OSquareArg,CSquare,commaSkip);
    return new T.C(c.withArity(ts.size()), of(ts));    
  }
  TName parseTName(){
    var c= expect("type name", Token.typeName);
    if(names.XIn(c.content())){ throw errFactory().typeNameConflictsGeneric(c,span(c).get()); }
    var s= c.content();
    if(s.contains("._")){ throw errFactory().privateTypeName(c,span(c).get()); }
    if(!s.startsWith("\"")){ return new TName(s,0,"",pos(c)); }
    s = new ClassicDecoder(
      s.substring(1, s.length()-1), 0, this::interBadUnicode).of();
    return new TName(c.content(),0,s,pos(c));
  }
  T parseT(){ //T    ::= C | RC C | X | RC X | read/imm X
    if(fwdIf(peek(ReadImm))){ return new T.ReadImmX(parseTX()); }
    Optional<RC> rc= parseOptRC();
    if(peekIf(this::isTName)){ return new T.RCC(rc,parseC()); }
    T.X res= parseTX();
    return rc.map(r->(T)new T.RCX(r, res)).orElse(res);
  }
  T.X parseDecTX(boolean mustNew){
    var c= expect("Generic type name declaration", UppercaseId);
    if(mustNew && names.XIn(c.content())){ throw errFactory().nameRedeclared(c,span(c).get()); }
    if(!mustNew && !names.XIn(c.content())){ throw errFactory().genericNotInScope(c, span(c).get(), names.Xs()); }
    return new T.X(c.content(),pos(c));
  }
  T.X parseTX(){
    var c= expectValidate("type name", UppercaseId,_XId);
    if(!names.XIn(c.content())){ throw errFactory().genericNotInScope(c, span(c).get(), names.Xs()); }
    return new T.X(c.content(),pos(c));
  }
  E parsePost(E receiver){
    if(peek(UStrInterHash,UStrLine)){ return parseStrInter(false,of(receiver)); }
    if(peek(SStrInterHash,SStrLine)){ return parseStrInter(true, of(receiver)); }
    MName m= parseMName();
    Optional<E.CallSquare> sq= parseIf(peek(_SquareGroup),()->parseGroup("method call generic parameters",Parser::parseCallSquare));
    Pos pos= pos();
    if(peek(_RoundGroup)){
      List<E> es = parseGroupSep("","arguments list",Parser::parseE,ORound,CRound,commaExp);
      return new E.Call(receiver, m.withArity(es.size()), sq, true, empty(), es, pos);
    }
    Optional<XPat> xpat= parseIf(eqSugar(),()->fwd(parseXPat()));    
    if (end() || hasPost()){
      if (xpat.isPresent()){ throw errFactory().missingExprAfterEq(remainingSpan()); }
      return new E.Call(receiver, m, sq, false,empty(),List.of(), pos);
    }
    List<E> atom= List.of(parseAtom());//we need to avoid parsing the posts
    updateNames(names.add(xsOf(xpat).toList(), List.of()));//zero if xpat is empty
    return new E.Call(receiver, m.withArity(xpat.isPresent()?2:1), sq, false,xpat,atom,pos);//note: arity 2 is special case for = sugar 
  }
  boolean eqSugar(){ return peekOrder(t->t.is(LowercaseId,_CurlyGroup),t->t.is(Eq)); }
  MName parseMName(){
    String n= expect("method name", DotName,Op).content();
    return new MName(n,0);
    }
  MName parseDotName(){ return new MName(expect("method name",DotName).content(),0); }
  XPat parseXPat(){
    if(peek(LowercaseId)){ return new XPat.Name(parseDecX()); }
    if(!peek(_CurlyGroup)){ throw errFactory().parameterNameExpected(remainingSpan());}
    var res= parseGroup("nominal pattern",Parser::parseDestruct);
    var errSpaceBeforeId= peek(LowercaseId,UnsignedInt,UppercaseId);
    if(!errSpaceBeforeId){return res;}
    throw errFactory().spaceBeforeId(span(peek().get()).get(),peek().get().content());
  }
  XPat.Destruct parseDestruct(){
    expect("nominal pattern",OCurly);
    var last= expectLast("nominal pattern",CCurly,CCurlyId).content();
    Optional<String> id= parseIf(last.length()>1,()->last.substring(1));//"}" or "}id"
    List<List<MName>> chains= splitBy("nominal pattern",commaSkip,Parser::parseChain);
    return new XPat.Destruct(chains, id);
  }
  List<MName> parseChain(){ return splitBy("",anyLeft,Parser::parseDotName); }
  
  E.CallSquare parseCallSquare(){
    expect("method call generic type argument",OSquareArg);
    expectLast("method call generic type argument",CSquare);
    var rc= parseOptRC();
    if(end()){ return new E.CallSquare(rc, List.of()); }
    if(rc.isPresent()){ expect("method call generic type argument",Comma); }
    List<T> ts= splitBy("genericTypes",commaSkip,Parser::parseT);
    return new E.CallSquare(rc, ts);
  }
  E.StringInter parseStrInter(boolean isSimple, Optional<E> receiver){
    Pos pos= pos();
    Predicate<Token> cond= isSimple
      ? t->t.is(SStrInterHash,SStrLine)
      : t->t.is(UStrInterHash,UStrLine);
    List<StringInfo> contents= new ArrayList<>();
    while(peekIf(cond)){ contents.add(new StringInfo(expectAny(""),this::interOnNoClose,this::interOnNoOpen,this::interOnMoreOpen,this::interBadUnicode)); }
    List<Integer> hashes= contents.stream().map(i->i.hashCount).toList();
    List<String> parts= StringInfo.mergeParts(contents);
    List<E> es= contents.stream()
      .flatMap(i->IntStream.range(0,i.inter.size()).mapToObj(
        j->Parse.from(span().fileName(),names,i.inter.get(j),i.line,i.col+i.starts.get(j))))
      .toList();
    return new E.StringInter(isSimple,receiver,hashes,parts, es, pos);
  }
  Span lastT(int i,int j){
    setIndex(index()-1);
    var t= expectAny("");
    var fn= span().fileName();
    assert j>i;
    return new Span(fn,t.line(), t.column()+i, t.line(), t.column() + j);
  }
  void interOnNoClose(int i,int j){ throw errFactory().noClose(lastT(i,j)); }
  void interOnNoOpen(int i,int j){ throw errFactory().noOpen(lastT(i,j)); }
  void interOnMoreOpen(int i,int j){ throw errFactory().moreOpen(lastT(i,j)); }
  void interBadUnicode(int i, int j, String msg){throw errFactory().badUnicode(lastT(i,j),msg);}
  E.Implicit parseImplicit(){ return new E.Implicit(pos(expect("",ColonColon))); }
  E.Round parseRound(){
    expect("expression in round parenthesis",ORound);
    expectLast("expression in round parenthesis",CRound);
    return new E.Round(parseE());
    }
  E.X parseX(){
    var x= expect("parameter name",LowercaseId);
    if(!names.xIn(x.content())){ throw errFactory().nameNotInScope(x, span(x).get(), names.xs()); } 
    return new E.X(x.content(),pos(x));
  }
  E.X parseDecX(){
    var x= expect("parameter declaration",LowercaseId);
    if(names.xIn(x.content())){ throw errFactory().nameRedeclared(x,span(x).get()); }
    return new E.X(x.content(),pos(x));
  }
  E.Literal parseLiteral(boolean top, boolean typed){
    Pos pos= pos();
    Token start= expect("object literal",OCurly);
    Token end= expectLast("object literal",CCurly);
    Optional<E.X> thisName= empty();
    if(fwdIf(peek(BackTick))){
      var n= parseDecX();
      thisName = of(n);
      if(top && !n.name().equals("this")){
        var s= span(n.pos(),n.name().length());
        throw errFactory().badTopSelfName(s, n.name());
      }
      updateNames(names.add(List.of(thisName.get().name()),List.of()));
      }
    if (top && thisName.isEmpty()){ updateNames(names.add(List.of("this"),List.of())); }
    List<M> ms= splitBy("method declaration",semiSkip,p->p.parseMethod(top,typed));
    checkRedeclaration(start, end, ms, pos);
    return new E.Literal(thisName,ms,pos);
    }
  private void checkRedeclaration(Token start, Token end, List<M> ms, Pos pos){
    List<MName> names= ms.stream()
      .flatMap(m->m.sig().flatMap(s->s.m()).stream()).toList();
    long count1= names.stream().distinct().count();
    if (names.size() > count1){ throw errFactory().methNameRedeclared(ms,names,span(start,end).get()); }
    List<Integer> noNames= ms.stream()
      .map(errFactory()::parCount).filter(i->i != -1).toList();
    long count2= noNames.stream().distinct().count();
    if (noNames.size() > count2){ throw errFactory().methNoNameRedeclared(ms,noNames,span(start,end).get()); }
  }
  Stream<String> xsOf(Optional<XPat> xp){
    if(xp.isEmpty()){ return Stream.of(); }
    return xp.get().parameterNames();
  }
  String repeated(List<String> ss){
    var seen= new java.util.HashSet<String>();
    for (var s : ss){ if (!seen.add(s)){ return s; } }
    return "";
  }
  void checkValidNew_xs(List<String> xs){
    var x= repeated(xs);
    if (!x.isEmpty()){ throw errFactory().duplicateParamInMethodSignature(span(), x); }
  }
  void checkValidNew_Xs(List<String> Xs){
    var x= repeated(Xs);
    if (!x.isEmpty()){ throw errFactory().duplicateGenericInMethodSignature(span(), x); }
  }
  void checkTyped(Sig sig, boolean implicit){
    boolean err= false;
    boolean mustType= sig.t().isPresent()
      || sig.bs().isPresent()
      || sig.parameters().stream().anyMatch(p->p.t().isPresent());
    
    if (!mustType){ err= sig.rc().isPresent(); }
    if (mustType){ err= !sig.fullyTyped() || implicit; }
    if (err){ throw errFactory().disallowedSig(span(),sig); }
  }
  M parseMethod(boolean top, boolean typed){
    var res= parseMethodAux(top,typed);
    expectEnd("semicolon or closed curly", SemiColon,CCurly);
    return res;
  }
  M parseMethodWithSig(Sig sig, Pos pos, boolean typed){
    var xs= sig.parameters().stream().flatMap(p->xsOf(p.xp())).toList();
    var Xs= sig.bs().orElse(List.of()).stream().map(b->b.x().name()).toList();
    updateNames(names.add(xs,Xs));
    var res= new M(of(sig),of(parseMethodBody()),pos);
    if (!typed){ checkTyped(sig, res.hasImplicit()); }
    return res;
  }
  M parseMethodAux(boolean top, boolean typed){//assumes to be called on only the tokens of this specific method
    Pos pos= pos();    
    Optional<M> m= parseFront("method signature",false,arrowSkip,Parser::parseSig)
      .map(s->parseMethodWithSig(s,pos,typed));
    if (m.isPresent()){ return m.get(); }
    boolean hasSig= peek(DotName,Op,RCap)
      || peekOrder(t->t.is(RCap), t->t.is(DotName,Op));
    if(!hasSig){ return new M(empty(),of(parseMethodBody()),pos); }
    Sig sig= parseSig();
    var res= new M(of(sig),empty(),pos);
    if (!typed){ checkTyped(sig,false); }
    if(!top){ throw errFactory().noAbstractMethod(res.sig().get(),span(pos, 100)); }
    return res;
  }
  E parseMethodBody(){
    guard(Parser::checkAbruptExprEnd);
    return  parseRemaining("method body",Parser::parseE); 
    }
  Sig parseSig(){
    var rcSpan= peek().map(t->span(t).orElse(span()));
    var rc= parseOptRC();
    var invalid= rc.map(_rc->_rc==RC.mutH || _rc==RC.readH || _rc==RC.iso).orElse(false);
    if(invalid){ throw errFactory().disallowedReadHMutH(rcSpan.get(), rc.get()); }
    var m= parseIf(peek(DotName,Op),this::parseMName);
    var bs= parseIf(peek(_SquareGroup),()->parseBs(true));
    var Xs= bs.orElse(List.of()).stream().map(b->b.x().name()).toList();
    checkValidNew_Xs(Xs);
    updateNames(names.addXs(Xs));//added both inside and outside since different parsers
    boolean hasPar=peek(_RoundGroup);
    List<Parameter> ps= hasPar
      ?parseGroupSep("","method parameters declaration",Parser::parseParameter,ORound,CRound,commaSkip)
      :parseNakedParameters();
    Optional<T> t= parseOptT();
    m = m.map(_m->_m.withArity(ps.size()));
    var xs= ps.stream().flatMap(p->xsOf(p.xp())).toList();    
    checkValidNew_xs(xs);
    return new Sig(rc,m,bs,hasPar,ps,t);
  }
  List<Parameter> parseNakedParameters(){
    if(peek(Colon)){ return List.of(); }
    return splitBy("method parameters declaration",commaSkip,Parser::parseParameter);
    }
  Optional<T> parseOptT(){ return parseIf(fwdIf(peek(Colon)),this::parseT); }
  Parameter parseParameter(){
    Optional<XPat> x= parseIf(peek(LowercaseId,_CurlyGroup),this::parseXPat);
    if(x.isPresent()){ return new Parameter(x, parseOptT()); }
    T t= parseT();
    return new Parameter(x,of(t));
  }
  List<B> parseBs(boolean mustNew){ 
    return parseGroup("",p->{
      p.expect("generic bounds declaration",OSquareArg);
      p.expectLast("generic bounds declaration",CSquare);
      var res= p.splitBy("generic bounds declaration",commaB,pi->pi.parseB(mustNew));
      var Xs= res.stream().map(b->b.x().name()).toList();
      checkValidNew_Xs(Xs);
      return res;
    });
  }
  B parseB(boolean mustNew){
    T.X x= parseDecTX(mustNew);
    if(end()){ return new B(x,new B.RCS(List.of())); }
    expect("generic bounds",Colon);
    if(!peek(Op)){ return new B(x,new B.RCS(parseRCs())); }
    var opT= expect("** or *",Op);
    String op= opT.content();
    if(op.equals("**")){ return new B(x,new B.StarStar()); }
    if(op.equals("*")){ return new B(x,new B.Star()); }
    throw errFactory().badBound(x.name(),span(opT).get());
  }
  List<RC> parseRCs(){ return splitBy("generic bounds declaration",commaSkip,Parser::parseRC); }
  
  List<T.C> parseImpl(){
    int start= index();
    var res= parseFront("",true,
      curlyRight,
      p->p.splitBy("super types declaration",commaSkip,Parser::parseC)
    ).get();
    var dup= res.stream().distinct().count() < res.size();
    if (dup){ throw errFactory().duplicatedImpl(res, spanAround(back(start), index())); }
    return res;
  }
  public static Span span(Pos pos, int size){
    return new Span(pos.fileName(), pos.line(), pos.column(),pos.line(),pos.column()+size); 
  }
  Declaration parseDeclaration(boolean top){
    var c= parseTName();
    var _= expectValidate(back("simple type name"), UppercaseId,_XId); //to get error if of form foo.Bar
    Optional<List<B>> bs= parseIf(peek(_SquareGroup),()->this.parseBs(top));
    if(bs.isPresent()){
      var Xs= bs.get().stream().map(b->b.x().name()).toList();
      if (top){ updateNames(names.addXs(Xs)); }
      else    { updateNames(names.setFunnelledXs(Xs)); }
      c = c.withArity(bs.get().size());
    }
    expect("type declaration (:) symbol",Colon);
    
    List<T.C> cs= this.parseImpl();
    assert peek(_CurlyGroup);
    E.Literal l= parseGroup("type declaration body",p->p.parseLiteral(top,true));
    return new Declaration(c,bs,cs,l);
  }
  FileFull parseFileFull(){
    expect("",_SOF);
    expectLast("",_EOF);
    var head=parseFrontOrAll("file header", headEnd,Parser::parseHeader);
    List<Declaration> ds= splitBy("type declaration",curlyLeft,p->p.parseDeclaration(true));
    String pkg= head.pkg.isEmpty()?"":head.pkg.getFirst();
    return new FileFull(pkg,head.role.stream().findFirst(),List.copyOf(head.map),List.copyOf(head.use),ds);
  }
  boolean peekValidate(TokenKind kind, TokenKind validation){
    Optional<Token> res= peek();
    if(res.isEmpty()){ return false; }
    try{ TokenKind.validate(res.get().content(),"",validation); return true; }
    catch(IllegalArgumentException iae){ return false; } 
  }
  Token expectValidate(String human, TokenKind kind, TokenKind validation){
    var ok= peekValidate(kind, validation);    
    if (ok){ return expect(human,kind); }
    try{ expect(human,validation); }
    catch(FearlessException fe){ throw fe.addSpan(spanAround(index(),index()));}
    throw Bug.unreachable();
  }
  void parsePackage(HeadAcc acc){
    var empty= acc.pkg.isEmpty() && acc.role.isEmpty() && acc.map.isEmpty() && acc.use.isEmpty();
    if(!empty){ throw errFactory().disallowedPackageNotEmpty(spanLast()); }
    var pkgName= expectValidate("package name",LowercaseId,_pkgName);
    acc.pkg.add(pkgName.content());
  }
  void parseRole(HeadAcc acc){
    if(!acc.role.isEmpty()){ throw errFactory().disallowedRoleNotEmpty(spanLast()); }
    var roleName= expectValidate("\"role\" keyword",LowercaseId,_roleName).content();
    int num= Integer.parseInt(roleName.substring(roleName.length()-3));
    roleName= roleName.substring(0,roleName.length()-3);
    acc.role.add(new FileFull.Role(FileFull.RoleName.valueOf(roleName),num));
  }
  void parseMap(HeadAcc acc){
    var in= expectValidate("package name",LowercaseId,_pkgName).content();
    expectValidate("\"as\" keyword",LowercaseId,_as);
    var out= expectValidate("package name",LowercaseId,_pkgName).content();
    expectValidate("\"in\" keyword",LowercaseId,_in);
    var target= expectValidate("package name",LowercaseId,_pkgName).content();
    var dup= acc.map.stream().anyMatch(m->m.in().equals(in) && m.target().equals(target));
    if(dup){ throw errFactory().duplicatedMap(spanLast(), "("+target+","+in+")"); }
    acc.map.add(new FileFull.Map(in,out,target));
  }
  void parseUse(HeadAcc acc){
    var t1= parseTName();
    expectValidate("\"as\" keyword",LowercaseId,_as);
    var t2= expectValidate("simple type name", UppercaseId,_XId).content();
    var dupS= acc.use.stream().anyMatch(u->u.in().equals(t1));
    var dupD= acc.use.stream().anyMatch(u->u.out().equals(t2));
    if(dupS){ throw errFactory().duplicatedUseSource(spanLast(), t1.s()); }
    if(dupD){ throw errFactory().duplicatedUseDest(spanLast(), t2); }
    acc.use.add(new FileFull.Use(t1,t2));
  }
  record HeadAcc(ArrayList<String>pkg, ArrayList<FileFull.Role>role,ArrayList<FileFull.Map>map,ArrayList<FileFull.Use>use){
    HeadAcc(){this(new ArrayList<>(),new ArrayList<>(),new ArrayList<>(),new ArrayList<>());}
  }
  Void endHE(){ expectEnd("semicolon", SemiColon); return null;}
  Void parseHeaderElement(HeadAcc acc){
    if(fwdIf(peekValidate(LowercaseId,_package))){ parsePackage(acc); return endHE(); }
    if(fwdIf(peekValidate(LowercaseId,_role))){ parseRole(acc); return endHE(); }
    if(fwdIf(peekValidate(LowercaseId,_map))){ parseMap(acc); return endHE(); }
    if(fwdIf(peekValidate(LowercaseId,_use))){ parseUse(acc); return endHE(); }
    if(acc.pkg.isEmpty()){ expectValidate("\"package\" keyword",LowercaseId,_package); }
    expect("header keyword \"role\", \"map\" or \"use\"",_role,_map,_use);
    throw Bug.unreachable();
  }
  HeadAcc parseHeader(){
    HeadAcc acc= new HeadAcc();
    if (!peek(LowercaseId)) { return acc; }
    expectLast("semicolon", SemiColon);
    splitBy("header element", semiSkip,p->p.parseHeaderElement(acc));
    return acc;
  }
  E parseEFull(){
    expect("",_SOF);
    expectLast("",_EOF);
    guard(Parser::checkAbruptExprEnd);
    return parseE(); 
  }
  boolean isTName(Token t){ return t.is(UppercaseId,SignedFloat,SignedInt,UnsignedInt,SignedRational,SStr,UStr) && !names.XIn(t.content()); }
  Pos pos(){
    Span s= spanAround(index(),index());
    return new Pos(s.fileName(),s.startLine(),s.startCol()); 
  }
  Pos pos(Token t){ return new Pos(span().fileName(),t.line(),t.column()); }
  <R> Optional<R> parseIf(boolean cond, Supplier<R> s){
    if(!cond){ return empty(); }
    return of(s.get());
  }
  int onCommaExp(){
    boolean inColon= false;
    while(!end()){
      var t= expectAny("");
      if(t.is(Comma) && !inColon){ return 1; }
      if(t.is(_CurlyGroup)){ inColon = false; }
      if(t.is(Colon)){ inColon = true;}
    }
    return 0;
  }
  int onCommaB(){
    while(!end()){
      var t= expectAny("");
      if(t.is(Comma) && !peek(RCap)){ return 1; }
    }
    return 0;
  }
  int headEnd(){
    while(!end() && !isDec()){ expectAny(""); }
    return 0;
  }
  public void checkAbruptExprEnd(){
    absurd();
    eatAtom();    
    while (!end()){ eatPost(); eatAtom(); }
  }
  private void absurd(){
    var absurd= peek(Colon,Arrow,BackTick,Eq,Comma,SemiColon);//will add more when we find other absurd cases
    if(absurd){ expect("expression",LowercaseId,UppercaseId,ORound,OCurly); }
  }
  private void eatAtom(){
    if(peekOrder(t->t.is(LowercaseId,_CurlyGroup),t->t.is(Eq))){ expectAny("");expectAny(""); }
    var simple= peek(LowercaseId,_RoundGroup,ColonColon,_CurlyGroup);
    if (fwdIf(simple)){ return; }
    var interp= peek(UStrInterHash,UStrLine,SStrInterHash,SStrLine);
    if(interp){ while(fwdIf(peek(UStrInterHash,UStrLine,SStrInterHash,SStrLine))){} return; }
    fwdIf(peek(RCap));
    fwdIf(peekOrder(t->t.isTypeName()));
    fwdIf(peek(_SquareGroup));
    if(fwdIf(peek(Colon))){ while(fwdIf(peek(Comma,UppercaseId,_SquareGroup))){} }
    fwdIf(peek(_CurlyGroup));
  }
  private void eatPost(){
    if(fwdIf(hasPost())){ fwdIf(peek(_SquareGroup)); return; }
    var signed= peek(SignedInt,SignedFloat,SignedRational);
    if (signed){ throw this.errFactory().signedLiteral(spanAround(index(),index()),expectAny("")); }
    throw this.errFactory().missingSemicolonOrOperator(spanAround(index(),index()));    
  }
  interface Cut extends NextCut<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>{}
  Cut commaSkip=  p->p.splitOn(Skipped,Comma);
  Cut semiSkip=   p->p.splitOn(Skipped,SemiColon);
  Cut arrowSkip=  p->p.splitOn(Skipped,Arrow);
  Cut curlyLeft=  p->p.splitOn(Left,_CurlyGroup);
  Cut curlyRight= p->p.splitOn(Right,_CurlyGroup);
  Cut headEnd=    Parser::headEnd;
  Cut commaB=     Parser::onCommaB;
  Cut commaExp=   Parser::onCommaExp;
  Cut anyLeft=    p->{ p.expectAny(""); return 0; };  
  @Override public FearlessErrFactory errFactory(){ return new FearlessErrFactory(); }
}