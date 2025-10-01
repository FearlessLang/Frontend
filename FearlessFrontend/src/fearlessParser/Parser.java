package fearlessParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Stream;

import fearlessParser.XPat.Destruct;
import fearlessParser.XPat.Name;
import files.Pos;
import message.FearlessErrFactory;
import message.FearlessException;
import metaParser.MetaParser;
import metaParser.Span;

import static fearlessParser.TokenKind.*;
import static java.util.Optional.of;
import static java.util.Optional.empty;
import static metaParser.MetaParser.SplitMode.*;


public class Parser extends MetaParser<Parser,Token,TokenKind,FearlessException>{
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
  E parseAtom(){
    if(peek(LowercaseId)){ return parseX(); }
    if(peek(_RoundGroup)){ return parseGroup("expression in round parenthesis",Parser::parseRound); }
    if(peek(ColonColon)){ return parseImplicit(); }
    if(peek(UStrInterHash,UStrLine)){ return parseStrInter(false,empty()); }
    if(peek(SStrInterHash,SStrLine)){ return parseStrInter(true,empty()); }
    if(peek(_CurlyGroup)){ return parseGroup("object literal", Parser::parseLiteral); }
    var rcSpan= peek().map(t->span(t).orElse(span()));
    Optional<RC> rc= parseOptRC();
    var invalid= rc.map(_rc->_rc==RC.mutH || _rc==RC.readH).orElse(false);
    if(invalid){ throw errFactory().disallowedReadHMutH(rcSpan.get(), rc.get()); }
    var isDec=//Dec starts with D[Bs]: or D:
         peekOrder(t->t.isTypeName(), t->t.is(_SquareGroup), t->t.is(Colon))
      || peekOrder(t->t.isTypeName(), t->t.is(Colon));
    if(isDec){ return new E.DeclarationLiteral(rc,parseDeclaration()); }
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
    return new E.TypedLiteral(c,of(parseGroup("typed literal",Parser::parseLiteral)),pos);
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
    return new TName(c.content(),0);
  }
  T parseT(){ //T    ::= C | RC C | X | RC X | read/imm X
    if(fwdIf(peek(ReadImm))){ return new T.ReadImmX(parseTX()); }
    Optional<RC> rc= parseOptRC();
    if(peekIf(this::isTName)){ return new T.RCC(rc,parseC()); }
    T.X res= parseTX();
    return rc.map(r->(T)new T.RCX(r, res)).orElse(res);
  }
  T.X parseDecTX(){
    var c= expect("Generic type name declaration", UppercaseId);
    if(names.XIn(c.content())){ throw errFactory().nameRedeclared(c,span(c).get()); }
    return new T.X(c.content());
  }
  T.X parseTX(){
    var c= expect("type name", UppercaseId);
    if(!names.XIn(c.content())){ throw errFactory().genericNotInScope(c,span(c).get(), names.Xs()); }
    return new T.X(c.content());
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
    var res= parseGroup("nominalPattern",Parser::parseDestruct);
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
    while(peekIf(cond)){ contents.add(new StringInfo(expectAny("").content())); }
    List<Integer> hashes= contents.stream().map(i->i.hashCount).toList();
    List<String> parts= StringInfo.mergeParts(contents);
    List<E> es= contents.stream()
      .flatMap(i->i.inter.stream())
      .map(s->Parse.from(span().fileName(),names,s,pos.line(),pos.column()))
      .toList();
    return new E.StringInter(isSimple,receiver,hashes,parts, es, pos);
  }
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
  E.Literal parseLiteral(){
    Pos pos= pos();
    expect("object literal",OCurly);
    expectLast("object literal",CCurly);
    Optional<E.X> thisName= empty();
    if(fwdIf(peek(BackTick))){
      thisName = of(parseDecX());
      updateNames(names.add(List.of(thisName.get().name()),List.of()));
      }
    List<M> ms= splitBy("method declaration",semiSkip,Parser::parseMethod);
    return new E.Literal(thisName,ms,pos);
    }
  Stream<String> xsOf(Optional<XPat> xp){
    if(xp.isEmpty()){ return Stream.of(); }
    var v= new XPatVisitor<Stream<String>>(){
      @Override public Stream<String> visitXPatName(Name n){
        return Stream.of(n.x().name());
      }
      @Override public Stream<String> visitXPatDestruct(Destruct d){
        String id= d.id().orElse("");
        return d.extract().stream().map(e->e.getLast().s().substring(1)+id);
      }
    };
    return xp.get().accept(v);
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
  M parseMethod(){//assumes to be called on only the tokens of this specific method
    Optional<Sig> sig= parseUpTo("method signature",arrowSkip,Parser::parseSig);
    if(sig.isPresent()){
      var xs= sig.get().parameters().stream().flatMap(p->xsOf(p.xp())).toList();
      var Xs= sig.get().bs().orElse(List.of()).stream().map(b->b.x().name()).toList();
      updateNames(names.add(xs,Xs));
      return new M(sig,of(parseMethodBody()));
    }
    boolean hasSig= peek(DotName,Op,RCap)
      || peekOrder(t->t.is(RCap), t->t.is(DotName,Op));
    if(!hasSig){ return new M(empty(),of(parseMethodBody())); }
    return new M(of(parseSig()),empty());    
  }
  E parseMethodBody(){
    guard(Parser::checkAbruptExprEnd);
    return  parseRemaining("method body",Parser::parseE); 
    }
  Sig parseSig(){
    var rc= parseOptRC();
    var m= parseIf(peek(DotName,Op),this::parseMName);
    var bs= parseIf(peek(_SquareGroup),this::parseBs);
    boolean hasPar=peek(_RoundGroup);
    List<Parameter> ps= hasPar
      ?parseGroupSep("","method parameters declaration",Parser::parseParameter,ORound,CRound,commaSkip)
      :parseNakedParameters();
    Optional<T> t= parseOptT();
    m = m.map(_m->_m.withArity(ps.size()));
    
    var xs= ps.stream().flatMap(p->xsOf(p.xp())).toList();
    var Xs= bs.orElse(List.of()).stream().map(b->b.x().name()).toList();
    checkValidNew_xs(xs);
    checkValidNew_Xs(Xs);

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
  List<B> parseBs(){ return parseGroupSep("","generic bounds declaration",Parser::parseB, OSquareArg, CSquare, commaB); }
  B parseB(){//note: not always a single B on the tokens
    T.X x= parseDecTX();
    if(end()){ return new B(x,new RCS(List.of())); }
    expect("generic bounds",Colon);
    if(!peek(Op)){ return new B(x,new RCS(parseRCs())); }
    var opT= expect("** or *",Op);
    String op= opT.content();
    if(op.equals("**")){ return new B(x,new StarStar()); }
    if(op.equals("*")){ return new B(x,new Star()); }
    throw errFactory().badBound(x.name(),span(opT).get());
  }
  List<RC> parseRCs(){ return splitBy("generic bounds declaration",commaSkip,Parser::parseRC); }
  
  List<T.C> parseImpl(){
    return parseUpTo("",
      curlyRight,
      p->p.splitBy("super types declaration",commaSkip,Parser::parseC)
    ).get();
  }
  Declaration parseDeclaration(){
    var c= parseTName();
    Optional<List<B>> bs= parseIf(peek(_SquareGroup),this::parseBs);
    if(bs.isPresent()){
      var Xs= bs.get().stream().map(b->b.x().name()).toList();
      updateNames(names.addXs(Xs));
      c = c.withArity(bs.get().size());
    }
    expect("type declaration (:) symbol",Colon);
    //Dec in e will be parsed with empty Xs, funnelling handled by well formedness later
    Optional<List<T.C>> cs= parseIf(!peek(_CurlyGroup),this::parseImpl);
    assert peek(_CurlyGroup);
    E.Literal l= parseGroup("type declaration body",Parser::parseLiteral);
    return new Declaration(c,bs,cs.orElse(List.of()),l);
  }
  FileFull parseFileFull(){
    expect("",_SOF);
    expectLast("",_EOF);
    List<Declaration> ds= splitBy("type declaration",curlyLeft,Parser::parseDeclaration);
    return new FileFull(List.of(),ds);
    }
  E parseEFull(){
    expect("",_SOF);
    expectLast("",_EOF);
    return parseE();
    }
  boolean isTName(Token t){ return t.is(UppercaseId,Float,SignedInt,UnsignedInt,SignedRational,SStr,UStr) && !names.XIn(t.content()); }
  Pos pos(){ return new Pos(span().fileName(),span().startLine(),span().startCol()); }
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
  public void checkAbruptExprEnd(){
    absurd();
    eatAtom();    
    while (!end()){ eatPost(); eatAtom(); }
  }
  private void absurd(){
    var absurd= peek(Colon,Arrow);//will add more when we find other absurd cases
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
    if(!hasPost()){
      throw this.errFactory().missingSemicolonOrOperator(spanAround(index(),index())); }
    expectAny("");
    fwdIf(peek(_SquareGroup));
  }

  NextCut<Parser,Token,TokenKind,FearlessException> commaSkip=  p->p.splitOn(Skipped,Comma);
  NextCut<Parser,Token,TokenKind,FearlessException> semiSkip=   p->p.splitOn(Skipped,SemiColon);
  NextCut<Parser,Token,TokenKind,FearlessException> arrowSkip=  p->p.splitOn(Skipped,Arrow);
  NextCut<Parser,Token,TokenKind,FearlessException> curlyLeft=  p->p.splitOn(Left,_CurlyGroup);
  NextCut<Parser,Token,TokenKind,FearlessException> curlyRight= p->p.splitOn(Right,_CurlyGroup);
  NextCut<Parser,Token,TokenKind,FearlessException> commaB=     Parser::onCommaB;
  NextCut<Parser,Token,TokenKind,FearlessException> commaExp=   Parser::onCommaExp;
  NextCut<Parser,Token,TokenKind,FearlessException> anyLeft=    p->{ p.expectAny(""); return 0; };
  
  @Override public FearlessErrFactory errFactory(){ return new FearlessErrFactory(); }
}