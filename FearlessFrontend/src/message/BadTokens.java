package message;

import static fearlessParser.TokenKind.*;
import java.util.Optional;
import java.util.stream.Stream;

import core.FearlessException;
import fearlessParser.Parser;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import fearlessParser.Tokenizer;
import metaParser.Message;
import metaParser.Span;
import metaParser.TokenProcessor;
import utils.Bug;

import static message.Err.*;

public final class BadTokens{
  private BadTokens(){}
  public static TokenProcessor.Map<Token, TokenKind, FearlessException, Tokenizer, Parser, FearlessErrFactory> badTokensMap(){
    return new TokenProcessor.Map<Token, TokenKind, FearlessException, Tokenizer, Parser, FearlessErrFactory>()
      .put(Ws,           (_,_,_)->Stream.empty())
      .put(LineComment,  (_,_,_)->Stream.empty())
      .put(BlockComment, (_,_,_)->Stream.empty())
      .put(BadUStrUnclosed, (idx, t, tz)->frontOrBack(idx,t,tz,'\"'))
      .put(BadSStrUnclosed, (idx, t, tz)->frontOrBack(idx,t,tz,'`'))
      .put(BadUnclosedBlockComment, (_, t, tz)->badBlockComment(tz,t))
      .put(BadUnopenedBlockCommentClose, BadTokens::strayBlockCommentCloser)
      .put(OSquareArg, BadTokens::squareAfterLiteral)
      .putStr(BadOSquare,Code.UnexpectedToken::of,"""
Here we expect "[" as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".
""","common ambiguities")
      .putStr(BadUppercaseId,Code.UnexpectedToken::of,"""
Package names are restricted to be valid filenames on all operating systems.
Names like aux, nul, lpt2 are invalid on Windows.
""","package names")
      .putStr(BadSStrQuote,Code.UnexpectedToken::of,"""
Simple string literals are of form `"..."`, not "'...'";
that is: use double quotes (`"`) instead of single quotes ("'").
""","common ambiguities")
;}
  private static Stream<Token> strayBlockCommentCloser(int idx, Token t, Tokenizer tokenizer){
    var file= tokenizer.fileName();
    var hit= findPseudoOpenerBefore(idx, tokenizer);
    var base= t.span(file);
    if (hit.isEmpty()){
      throw Code.UnexpectedToken
        .of("Unopened block comment close \"*/\".\nRemove it, or add a matching \"/*\" earlier on.")
        .addFrame("comments",base);
    }
    var h= hit.get();
    var s= h.span(file);
    assert s.isSingleLine();
    var line= s.startLine();
    var index= h.content().indexOf("/*");
    var primary= new Span(file,line, s.startCol()+index, base.endLine(), base.endCol());
    var where= "inside a"+describeFree(h);
    throw Code.UnexpectedToken.of(
      "Unopened block comment close \"*/\".\n"
    + "Found a \"/*\" " + where + " before this point.\n"
    + "Did you mean to place the opener outside the string/comment?")
      .addFrame("comments",primary);
  }
  private static Stream<Token> squareAfterLiteral(int idx, Token t, Tokenizer tz){
    var lit= tz.allTokens().get(idx - 1);
    var afterLiteral= lit.is(SStr,UStr,SignedInt,UnsignedInt,SignedFloat,UnSignedFloat);
    if (!afterLiteral){ return Stream.of(t); }
    var file= tz.fileName();
    var s= lit.span(file);
    var name= disp(lit.content());
    throw Code.UnexpectedToken.of(
      "Literal "+name+" is directly followed by \"[\".\n"
    + "Number and string literals take no generic arguments.\n"
    + "Remove the \"[...]\" after "+name+".")
      .addFrame("a literal",new Span(file,s.startLine(),s.startCol(),t.line(),t.span(file).endCol()));
  }
  public static String describeFree(Token t){
    return switch (t.kind()){
      case LineComment -> " line comment \"//\"";
      case BlockComment -> " block comment \"/* ... */\"";
      case UStr, SStr   -> " string literal";
      default -> throw Bug.of(t.toString());
    };
  }

  private static Optional<Token> findPseudoOpenerBefore(int idx, Tokenizer tz){
    var all= tz.allTokens();
    for (var j= idx - 1; j >= 0; j--){
      var p= all.get(j);
      if (p.is(BlockComment,_SOF)){ return Optional.empty(); }
      var hidesOpener= p.is(LineComment, UStr, SStr) && p.content().contains("/*");
      if (hidesOpener){ return Optional.of(p); }
    }
    throw Bug.unreachable();
  }
  private static String errStart(int quoteChar){
    return "String literal " + Message.displayChar(quoteChar)
    + " reaches the end of the line.\n";
  }
  private static FearlessException errNoInfo(Span at, int quoteChar){ return Code.UnexpectedToken.of(errStart(quoteChar)).addFrame("a string literal",at); }
  private static FearlessException errEatAfter(Span at, int quoteChar){
    return Code.UnexpectedToken.of(errStart(quoteChar)
    + "A comment opening sign is present later on this line; did you mean to close the string before it?"
      ).addFrame("a string literal", at);
  }
  private static FearlessException errEatBefore(Span at, int quoteChar){
    return Code.UnexpectedToken.of(errStart(quoteChar)
    + "A preceding block comment \"/* ... */\" on this line contains that quote.\n"
    + "Did it swallow the intended opening quote?"
      ).addFrame("a string literal",at);
  }
  private static Stream<Token> badBlockComment(Tokenizer tz, Token t){
    var file= tz.fileName();
    var s= t.span(file);
    var lineEnd= t.content().indexOf('\n');
    if (lineEnd != -1){ s= new Span(file,s.startLine(),s.startCol(),s.startLine(),s.startCol()+lineEnd); }
    throw Code.UnexpectedToken
      .of("Unterminated block comment. Add \"*/\" to close it.")
      .addFrame("a block comment", s);
  }
  private static Stream<Token> frontOrBack(int idx, Token t, Tokenizer tz, int quoteChar){
    var file= tz.fileName();
    var text= t.content();
    var b= t.span(file);
    assert b.isSingleLine();
    //If '//' or '/*' is inside the bad string, trim span to stop before it.
    var openSL= text.indexOf("//");
    var openML= text.indexOf("/*");
    var idxComment= openSL == -1 ? openML : openML == -1 ? openSL : Math.min(openSL, openML);
    if (idxComment != -1){
      var after= new Span(file, b.startLine(), b.startCol(), b.endLine(), b.startCol() + idxComment);
      throw errEatAfter(after, quoteChar);
    }
    var all= tz.allTokens();
    var j= idx - 1;
    while (j > 0 && !all.get(j).is(BlockComment)){ j -= 1; }
    var prev= all.get(j);
    if (!prev.is(BlockComment)){ throw errNoInfo(b, quoteChar); }
    var s= prev.span(file);
    if (s.endLine() != t.line()){ throw errNoInfo(b, quoteChar); }
    var quote= prev.content().lastIndexOf(quoteChar);
    var nl= prev.content().lastIndexOf('\n');
    var swallowedByComment= quote != -1 && quote > nl;
    if (!swallowedByComment){ throw errNoInfo(b, quoteChar); }
    var line= b.endLine();
    var endCol= b.startCol()+1;//invert the caret
    var startCol= s.endCol()-(prev.content().length()-quote);
    var before= new Span(file,line,startCol,line,endCol);
    throw errEatBefore(before, quoteChar);
  }
}