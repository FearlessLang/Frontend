package message;

import static fearlessParser.TokenKind.*;
import static message.Err.*;

import java.util.Locale;
import java.util.Optional;
import java.util.regex.Pattern;
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

public final class BadTokens{
  public static TokenProcessor.Map<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory> badTokensMap(){
    return new TokenProcessor.Map<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>()
      .put(Ws,           (_,_,_) -> Stream.of())
      .put(LineComment,  (_,_,_) -> Stream.of())
      .put(BlockComment, (_,_,_) -> Stream.of())
      .put(BadUStrUnclosed, (idx, t, tz) -> frontOrBack(idx, t, tz, '\"'))
      .put(BadSStrUnclosed, (idx, t, tz) -> frontOrBack(idx, t, tz, '`'))
      .put(BadUnclosedBlockComment, (_, t, tz) -> badBlockComment(tz, t))
      .put(BadUnopenedBlockCommentClose, BadTokens::strayBlockCommentCloser)
      .put(OSquareArg, BadTokens::squareAfterLiteral)
      .putStr(BadOSquare, Code.UnexpectedToken::of, """
A "[" must come right after a type name or a method name.
Valid: "Foo[Bar]", "x.foo[read]".
Invalid: "Foo [Bar]", "x.foo [read]".
""", "common ambiguities")
      .putStr(BadUppercaseId, Code.UnexpectedToken::of, """
Package names are restricted to be valid filenames on all operating systems.
Names like "aux", "nul", "lpt2" are invalid on Windows.
""", "package names")
      .put(BadSStrQuote, (_, t, tz) -> singleQuoteString(t, tz))
      .put(BadDotName, BadTokens::uppercaseMethodName)
      .putStr(BadDot, Code.UnexpectedToken::of, """
No space is allowed after ".".
""", "")
      .putStr(BadChar, Code.UnexpectedToken::of, """
This character can only appear inside comments and inside type names in quotes, like `"a@b"`.
""", "")
;}
  private static Stream<Token> uppercaseMethodName(int idx, Token t, Tokenizer tz){
    var c= t.content();
    var r= tz.allTokens().get(idx - 1).content();
    var at= t.span(tz.fileName());
    if (!r.matches("[A-Z][A-Za-z0-9_]*")){ throw Code.UnexpectedToken.of(disp(c)+" is not valid as a method name.").addFrame("a method name", at); }
    var fix= Pattern.compile("[A-Z]").matcher(c).replaceFirst(m -> m.group().toLowerCase(Locale.ROOT));
    var pkg= r.toLowerCase(Locale.ROOT);
    throw Code.UnexpectedToken.of(disp(r+c)+" is neither a type name nor a method call.\n"
      +"A package name and a method name start with a lowercase letter,\nas in "
      +disp(pkg+c)+" (type "+disp(c.substring(1))+" of package "+disp(pkg)+") and "
      +disp(r+fix)+" (method "+disp(fix)+" called on "+disp(r)+").").addFrame("a name", at);
  }
  private static Stream<Token> singleQuoteString(Token t, Tokenizer tz){
    var c= t.content();
    var in= c.substring(1, c.length()-1);
    throw Code.UnexpectedToken.of("Unrecognized text "+disp(c)+".\n"
      +"Single quotes do not form type names.\n"
      +"Type names in quotes use double quotes or backticks:\n"
      +"  \""+in+"\"\n"
      +"  `"+in+"`")
      .addFrame("common ambiguities", t.span(tz.fileName()));
  }
  private static Stream<Token> strayBlockCommentCloser(int idx, Token t, Tokenizer tokenizer){
    var file= tokenizer.fileName();
    var hit= findPseudoOpenerBefore(idx, tokenizer);
    var base= t.span(file);
    if (hit.isEmpty()){
      throw Code.UnexpectedToken
        .of("Unopened block comment close \"*/\".\nRemove it, or add a matching \"/*\" earlier on.")
        .addFrame("comments", base);
    }
    var h= hit.get();
    var s= h.span(file);
    assert s.isSingleLine();
    var line= s.startLine();
    var index= h.content().indexOf("/*");
    var primary= new Span(file, line, s.startCol()+index, base.endLine(), base.endCol());
    var where= "inside a"+describeFree(h);
    throw Code.UnexpectedToken.of(
      "Unopened block comment close \"*/\".\n"
    +"Found a \"/*\" "+where+" before this point.\n"
    +"The opener may belong outside the"+describeFree(h)+".")
      .addFrame("comments", primary);
  }
  private static Stream<Token> squareAfterLiteral(int idx, Token t, Tokenizer tz){
    var lit= tz.allTokens().get(idx - 1);
    var afterLiteral= lit.is(SStr, UStr, SignedInt, UnsignedInt, SignedFloat, UnSignedFloat);
    if (!afterLiteral){ return Stream.of(t); }
    var file= tz.fileName();
    var s= lit.span(file);
    var name= disp(lit.content());
    throw Code.UnexpectedToken.of(
      "Type "+name+" takes no generic type arguments.\n"
    +"Remove the \"[...]\" after "+name+".")
      .addFrame("a type name", new Span(file, s.startLine(), s.startCol(), t.line(), t.span(file).endCol()));
  }
  public static String describeFree(Token t){
    return switch (t.kind()){
      case LineComment -> " line comment \"//\"";
      case BlockComment -> " block comment \"/* ... */\"";
      case UStr, SStr   -> " type name in quotes";
      default -> throw Bug.of(t.toString());
    };
  }

  private static Optional<Token> findPseudoOpenerBefore(int idx, Tokenizer tz){
    var all= tz.allTokens();
    for (var j= idx - 1; j >= 0; j -= 1){
      var p= all.get(j);
      if (p.is(BlockComment, _SOF)){ return Optional.empty(); }
      var hidesOpener= p.is(LineComment, UStr, SStr) && p.content().contains("/*");
      if (hidesOpener){ return Optional.of(p); }
    }
    throw Bug.unreachable();
  }
  private static FearlessException strErr(Span at, int quoteChar, String more){
    return Code.UnexpectedToken.of("Quote "+Message.displayChar(quoteChar)+" is not closed before the end of the line.\n"+more).addFrame("a type name", at);
  }
  private static Stream<Token> badBlockComment(Tokenizer tz, Token t){
    var file= tz.fileName();
    var s= t.span(file);
    var lineEnd= t.content().indexOf('\n');
    if (lineEnd != -1){ s = new Span(file, s.startLine(), s.startCol(), s.startLine(), s.startCol()+lineEnd); }
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
      throw strErr(after, quoteChar, "A comment opening sign is present later on this line;\nthe quote may be meant to close before it.");
    }
    var all= tz.allTokens();
    var j= idx - 1;
    while (j > 0 && !all.get(j).is(BlockComment)){ j -= 1; }
    var prev= all.get(j);
    if (!prev.is(BlockComment)){ throw strErr(b, quoteChar, ""); }
    var s= prev.span(file);
    if (s.endLine() != t.line()){ throw strErr(b, quoteChar, ""); }
    var quote= prev.content().lastIndexOf(quoteChar);
    var nl= prev.content().lastIndexOf('\n');
    var swallowedByComment= quote != -1 && quote > nl;
    if (!swallowedByComment){ throw strErr(b, quoteChar, ""); }
    var line= b.endLine();
    var endCol= b.startCol()+1;//invert the caret
    var startCol= s.endCol()-(prev.content().length()-quote);
    var before= new Span(file, line, startCol, line, endCol);
    throw strErr(before, quoteChar, "A preceding block comment \"/* ... */\" on this line contains that quote.\nThat block comment may hold the intended opening quote.");
  }
}