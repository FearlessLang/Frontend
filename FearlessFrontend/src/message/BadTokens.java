package message;

import static fearlessParser.TokenKind.*;
import java.util.Optional;
import java.util.stream.Stream;

import fearlessParser.Parser;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import fearlessParser.Tokenizer;
import metaParser.Message;
import metaParser.Span;
import metaParser.TokenProcessor;
import utils.Bug;

public class BadTokens {
  public TokenProcessor.Map<Token, TokenKind, FearlessException, Tokenizer, Parser, FearlessErrFactory> badTokensMap(){
    return new TokenProcessor.Map<Token, TokenKind, FearlessException, Tokenizer, Parser, FearlessErrFactory>()
      .put(Ws,           (_,_,_) -> Stream.empty())
      .put(LineComment,  (_,_,_) -> Stream.empty())
      .put(BlockComment, (_,_,_) -> Stream.empty())
      .put(BadUStrUnclosed, (idx, t, tz) ->frontOrBack(idx,t,tz,'\"'))
      .put(BadSStrUnclosed, (idx, t, tz) ->frontOrBack(idx,t,tz,'`'))
      .put(BadUnclosedBlockComment, (_, t, tz) -> badBlockComment(tz,t))
      .put(BadUnopenedBlockCommentClose, this::strayBlockCommentCloser)
      .putStr(BadOpLine,Code.UnexpectedToken::of,"""
A "|" immediately before a quote starts a line string (e.g. |"abc or |`abc).
Operators can also contain "|", making it ambiguous what, for example, <--|`foo` means.
It could be the "<--" operator followed by |`foo` but also the "<--|" operator followed by `foo`. 
Please add spaces to disambiguate:  <--| `foo`   or   <-- |`foo`.
""","common ambiguities")    
      .putStr(BadOpDigit,Code.UnexpectedToken::of,"""
An operator followed by a digit is parsed as a signed number (e.g. "+5", "-3").
Operators can also contain "+" and "-", making it ambiguous what, for example, "<--5" means.
It could be the "<--" operator followed by "5" but also the "<-" operator followed by "-5".
Please add spaces to disambiguate:  "<-- 5"   or   "<- -5".
""","common ambiguities")
      .putStr(BadOSquare,Code.UnexpectedToken::of,"""
Here we expect "[" as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".
""","common ambiguities")
      .putStr(BadFloat,Code.UnexpectedToken::of,"""
Float literals must have a sign and digits on both sides of ".".
Examples: "+1.0", "-0.5", "+12.0e-3".
Fearless does not allow float literals of form "1.2" or ".2".
""","numbers")
      .putStr(BadRational,Code.UnexpectedToken::of,"""
Rational literals must have a sign.
Examples: "+1/2", "-3/4".
Fearless does not allow rational literals of form "1/2".
""","numbers")
      .putStr(BadUppercaseId,Code.UnexpectedToken::of,"""
Package names are restricted to be valid filenames on all operating systems.
Names like aux, nul, lpt2 are invalid on Windows.
""","package names")
      .putStr(BadSStrLineQuote,Code.UnexpectedToken::of,"""
Simple string lines start with " |` " or " #|` ", not " |' " or " #|' ";
that is: use back tick (`) instead of single quote (').
""","common ambiguities")
      .putStr(BadSStrQuote,Code.UnexpectedToken::of,"""
Simple string literals are of form " `...` ", not " '...' ";
that is: use back ticks (`) instead of single quotes (').
""","common ambiguities")
;}
  private Stream<Token> strayBlockCommentCloser(int idx, Token t, Tokenizer tokenizer){
    var file= tokenizer.fileName();
    var hit= findPseudoOpenerBefore(idx, tokenizer);
    var base= t.span(file);
    if (hit.isEmpty()){
      throw Code.UnexpectedToken
        .of("Unopened block comment close \"*/\".\nRemove it, or add a matching \"/*\" earlier on.")
        .addFrame("comments",base);
      }
    var h= hit.get();
    Span s= h.span(file);
    assert s.isSingleLine();
    int line= s.startLine();
    int index= h.content().indexOf("/*");
    Span primary= new Span(file,line, s.startCol()+index, base.endLine(), base.endCol());
    String where= "inside a"+describeFree(h);
   throw Code.UnexpectedToken.of(
     "Unopened block comment close \"*/\".\n"
   + "Found a \"/*\" " + where + " before this point.\n"
   + "Did you mean to place the opener outside the string/comment?")
     .addFrame("comments",primary);
  }
  public static String describeFree(Token t){
    return switch (t.kind()){
      case LineComment -> " line comment \"//\"";
      case BlockComment -> " block comment \"/* ... */\"";
      case UStr, SStr, UStrLine, SStrLine, UStrInterHash, SStrInterHash -> " string literal";
    default -> throw new Error(t.toString());
    };
  }
  
  private Optional<Token> findPseudoOpenerBefore(int idx, Tokenizer tz){
    var all= tz.allTokens();
    for (int j= idx - 1; j >= 0; j--){
      var p = all.get(j);
      if (p.is(BlockComment,_SOF)){ return Optional.empty(); }
      if (p.is(LineComment, UStr, SStr, UStrLine, SStrLine, UStrInterHash, SStrInterHash)){
        if (p.content().contains("/*")){ return Optional.of(p); }
      }
    }
    throw Bug.unreachable();
  }
  private String errStart(int quoteChar){
    return "String literal " + Message.displayChar(quoteChar)
    + " reaches the end of the line.\n";
  }
  private FearlessException errNoInfo(Span at, int quoteChar){ return Code.UnexpectedToken.of(errStart(quoteChar)).addFrame("a string literal",at); }
  private FearlessException errEatAfter(Span at, int quoteChar){
    return Code.UnexpectedToken.of(errStart(quoteChar)
    + "A comment opening sign is present later on this line; did you mean to close the string before it?"
      ).addFrame("a string literal", at);
    }
  private FearlessException errEatBefore(Span at, int quoteChar){
    return Code.UnexpectedToken.of(errStart(quoteChar)
    + "A preceding block comment \"/* ... */\" on this line contains that quote.\n"
    + "Did it swallow the intended opening quote?"
      ).addFrame("a string literal",at); 
    }
  private Stream<Token> badBlockComment(Tokenizer tz, Token t){
    var file = tz.fileName();
    Span s= t.span(file);
    int lineEnd= t.content().indexOf('\n');
    if (lineEnd != -1){ s = new Span(file,s.startLine(),s.startCol(),s.startLine(),s.startCol()+lineEnd); }
    throw Code.UnexpectedToken
      .of("Unterminated block comment. Add \"*/\" to close it.")
      .addFrame("a block comment", s);
    }
  private Stream<Token> frontOrBack(int idx, Token t, Tokenizer tz, int quoteChar){
    var file= tz.fileName();
    var text= t.content();
    Span b= t.span(file);
    assert b.isSingleLine();
    //If '//' or '/*' is inside the bad string, trim span to stop before it.
    int openSL = text.indexOf("//");
    int openML = text.indexOf("/*");
    int idxComment= openSL==-1?openML:openML==-1?openSL:Math.min(openSL, openML);
    if (idxComment >= 0){      
      Span after= new Span(file, b.startLine(), b.startCol(), b.endLine(), b.startCol() + idxComment);
      throw errEatAfter(after, quoteChar);      
    }
    var all= tz.allTokens();
    int j= idx - 1;
    while (j > 0 && !all.get(j).is(BlockComment)){ j -= 1; }
    Token prev= all.get(j);     
    if (!prev.is(BlockComment)){ throw errNoInfo(b, quoteChar); }
    Span s= prev.span(file);
    if (s.endLine() != t.line()){ throw errNoInfo(b, quoteChar); }
    int quote= prev.content().lastIndexOf(quoteChar);
    int nl= prev.content().lastIndexOf("\n");
    boolean swallowedByComment = quote > 0 && quote > nl;
    if (!swallowedByComment){ throw errNoInfo(b, quoteChar); }
    var line= b.endLine();
    var endCol= b.startCol()+1;//invert the caret
    var startCol= s.endCol()-(prev.content().length()-quote);
    Span before= new Span(file,line,startCol,line,endCol);
    throw errEatBefore(before, quoteChar);
  }
}