package message;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import fearlessParser.Parser;
import fearlessParser.RC;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import static fearlessParser.TokenKind.*;
import fearlessParser.Tokenizer;
import metaParser.ErrFactory;
import metaParser.Frame;
import metaParser.Message;
import metaParser.NameSuggester;
import metaParser.Span;
import metaParser.TokenProcessor;
import utils.Bug;

import static offensiveUtils.Require.*;

public class FearlessErrFactory implements ErrFactory<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>{

  @Override public FearlessException illegalCharAt(Span at, int cp, Tokenizer tokenizer){
    String head= "Illegal character "+Message.displayChar(cp);
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  @Override public FearlessException missing(Span at, String what, List<TokenKind> expectedLabels, Parser parser){
    assert nonNull(at,what,expectedLabels);
    String label= what.isBlank() ? "element" : what;
    String msg = "Missing " + label + ".\n"+expected(expectedLabels);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }

  @Override public FearlessException extraContent(Span from, Parser parser){
    assert nonNull(from);
    String msg= "Extra content in the current group";
    return Code.ExtraTokenInGroup.of(msg).addSpan(from);
  }
  @Override public FearlessException probeStalledIn(String groupLabel, Span at, int startIdx, int endIdx, Parser parser){
    String head= "Probe stalled while scanning " + groupLabel;
    return Code.ProbeError.of(head).addSpan(at);
  }
  @Override public FearlessException badProbeDropIn(String groupLabel, Span at, int startIdx, int endIdx, int drop, Parser parser){
    String msg= "Probe returned invalid drop=" + drop
      + " in " + groupLabel + " at [" + startIdx + ".." + endIdx + "]";
    return Code.ProbeError.of(msg).addSpan(at);
  }
  public FearlessException noClose(Span at){
    return Code.InterpolationNoClose.of(
      "Unclosed string interpolation placeholder").addSpan(at);
  }
  public FearlessException noOpen(Span at){
    return Code.InterpolationNoOpen.of(
      "Unopened string interpolation placeholder").addSpan(at);
  }
  public FearlessException moreOpen(Span at){
    return Code.InterpolationNoClose.of(
      "String interpolation placeholder opened inside interpolation expression.\n"
      +"Note: \"{\" can not be used in single \"#\" interpolation expressions. Use at least \"##\".").addSpan(at);
  }

  public FearlessException disallowedReadHMutH(Span at, RC rc){
    return Code.UnexpectedToken.of(
      "Capability "+rc+"""
       used.
      Capabilities readH and mutH are not allowed on closures
      Use one of read, mut, imm, iso.      
      """).addSpan(at);
  }
  public FearlessException nameNotInScope(Token name, Span at, Collection<String> inScope){
    return Code.UnexpectedToken.of(() -> {
      var maybe= NameSuggester.suggest(name.content(), inScope);
      var scope= inScope.isEmpty()
        ? "No names are in scope here.\n"
        : maybe.orElse("");
      return "Name "+Message.displayString(name.content())+" is not in scope\n" + scope;
    }).addSpan(at);
  }
  public FearlessException nameRedeclared(Token c, Span at){
    return Code.UnexpectedToken.of("Name "+Message.displayString(c.content())+" already in scope").addSpan(at);
  }
  public FearlessException typeNameConflictsGeneric(Token name, Span at){
    return Code.UnexpectedToken.of("Name "+Message.displayString(name.content())+" is used as a type name, but  "+Message.displayString(name.content())+" is already a generic type parameter in scope").addSpan(at);
  }
  public FearlessException missingExprAfterEq(Span at){
    return Code.UnexpectedToken.of("""
      Missing expression after "=" in the equals sugar.
      Use: ".m x = expression" or ".m {a,b} = expression".
      """).addSpan(at);
  }
  public FearlessException parameterNameExpected(Span at){
    return Code.UnexpectedToken.of("Parameter name expected").addSpan(at);
  }
  public FearlessException spaceBeforeId(Span at, String id){
    return Code.UnexpectedToken.of(
      "Found spacing between closed curly and destruct id \""+ id+"\"."
      +"\nThere need to be no space between the closed curly and the destruct id.")
      .addSpan(at);
  }
  public FearlessException badBound(String name, Span at){
    return Code.UnexpectedToken.of("Invalid bound for generic "+name+"""
      
      Only '*' or '**' are allowed here
      Write: X:*   meaning mut,read,imm
         or: X:**  meaning everything
      """).addSpan(at);
  }
  public FearlessException genericNotInScope(Token X, Span at, Collection<String> Xs){
    return Code.UnexpectedToken.of(() ->
      "Generic type "+Message.displayString(X.content())+" is not in scope\n" +
      (Xs.isEmpty()
        ? "No generic parameters are declared here."
        : "Declared generics: " + String.join(", ", Xs))).addSpan(at);
  }
  public FearlessException duplicateParamInMethodSignature(Span at, String name){
    return Code.UnexpectedToken.of(
      "A method signature cannot declare multiple parameters with the same name\n"
      +"Parameter "+Message.displayString(name)+" is repeated").addSpan(at);
  }
  public FearlessException duplicateGenericInMethodSignature(Span at, String name){
    return Code.UnexpectedToken.of(
      "A method signature cannot declare multiple generic type parameters with the same name\n"
      +"Generic type parameter "+Message.displayString(name)+" is repeated").addSpan(at);
  }
  public String context(){return "File ended while parsing a "; }
  private static String expected(Collection<? extends Object> items){ return expected("Expected ",items); }
  private static String expected(String pre, Collection<? extends Object> items){
    return (items.isEmpty() ? "" : (pre + _joinOrEmpty(items)));
  }

  private static String _joinOrEmpty(Collection<? extends Object> items){
    if (items.isEmpty()){ return ""; }
    var res= items.stream()
    .map(FearlessErrFactory::labelOf)
    .collect(Collectors.joining(", "))+".\n";
    if (items.size() == 1){ return res; }
    return "one of: "+res;
  }
  private static String describeFree(Token t){
    return switch (t.kind()){
      case LineComment -> " line comment \"//\"";
      case BlockComment -> " block comment \"/* ... */\"";
      case UStr, SStr, UStrLine, SStrLine, UStrInterHash, SStrInterHash -> " string literal";
    default -> throw new Error(t.toString());
  };
  }
  
  private static String labelOf(Object o){
    if (!(o instanceof fearlessParser.TokenKind tk)){ return String.valueOf(o); }
    var res= switch (tk) {
      case ORound -> "(";
      case CRound -> ")";
      case OCurly -> "{";
      case CCurly -> "}";
      case CCurlyId -> "}id";
      case OSquareArg -> "[";
      case CSquare -> "]";
      case Comma -> ",";
      case SemiColon -> ";";
      case ColonColon -> "::";
      case Colon -> ":";
      case Eq -> "=";
      case BackTick -> "`";
      case Arrow -> "->";
      case DotName -> ".name";
      case LowercaseId -> "name";
      case UppercaseId -> "TypeName";
      case UStr -> "\"...\"";
      case SStr -> "'...'";
      case UStrLine -> "|\"...";
      case SStrLine -> "|'...";
      case UStrInterHash -> "#|\"...";
      case SStrInterHash -> "#|'...";
      case RCap -> "reference capability";
      case ReadImm -> "read/imm";
      default -> tk.name();
    };
    return Message.displayString(res);
  }
  @Override public FearlessException unrecognizedTextAt(Span at, String what, Tokenizer tokenizer){
    String head= what.isBlank()
      ? "Unrecognized text."
      : "Unrecognized text " + Message.displayString(what)+".";
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  public FearlessException missingSemicolonOrOperator(Span at){
    return Code.MissingSeparator.of(
      "There is a missing \";\", operator or method name here or before").addSpan(at);
  }
  public FearlessException signedLiteral(Span at,Token t){
    return Code.UnexpectedToken.of(
      "Here "+Message.displayString(t.content())
      +" is seen as a single signed literal, not as a +/- operator followed by a literal.\n"
      +"Write \"1 + 2\" not \"1+2\".\n"
      +"Write \"+1 + +2\" not \"+1+2\".\n"
      +"Write \"+0.53 + +2.32\" not \"0.53+2.32\".\n"
      +"Write \"+3/2 + +4/5\" not \"3/2+4/5\"."
      ).addSpan(at);
  }

  public FearlessException badTokenAt(Span at, TokenKind kind, String text){
    String head = text.isBlank()
      ? "Unrecognized text."
      : "Unrecognized text " + Message.displayString(text) + ".";

    String hint= switch (kind){
      case BadOpLine -> """
A "|" immediately before a quote starts a line string (e.g. `|"abc"` or `|'abc'`).
Operators can also contain "|", making it ambiguous what, for example, `<--|'foo'` means.
It could be the "<--" operator followed by `|'foo'` but also the "<--|" operator followed by `'foo'`. 
Please add spaces to clarify:  `<--| 'foo'`   or   `<-- |'foo'`
""";
      case BadOpDigit -> """
An operator followed by a digit is parsed as a signed number (e.g. "+5", "-3").
Operators can also contain "+" and "-", making it ambiguous what, for example, "<--5" means.
It could be the "<--" operator followed by "5" but also the "<-" operator followed by "-5".
Please add spaces to clarify:  "<-- 5"   or   "<- -5"
""";
      case BadOSquare -> """
Here we expect "[" as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".
""";

      case BadFloat -> """
Float literals must have a sign and digits on both sides of '.'
Examples: "+1.0", "-0.5", "+12.0e-3".
Fearless does not allow float literals of form "1.2" or ".2"
""";

      case BadRational -> """
Rational literals must have a sign.
Examples: "+1/2", "-3/4".
Fearless does not allow rational literals of form "1/2"
""";
      default -> null;
    };

    String msg = (hint == null) ? head : head + "\n" + hint;
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  public Map<TokenKind, TokenProcessor<Token, TokenKind, FearlessException, Tokenizer, Parser, FearlessErrFactory>> badTokensMap(){
    return Map.ofEntries(
      Map.entry(Ws,           (_,_,_) -> Stream.empty()),
      Map.entry(LineComment,  (_,_,_) -> Stream.empty()),
      Map.entry(BlockComment, (_,_,_) -> Stream.empty()),

      Map.entry(BadUStrUnclosed, (idx, t, tz) ->frontOrBack(idx,t,tz,'\"')),
      Map.entry(BadSStrUnclosed, (idx, t, tz) ->frontOrBack(idx,t,tz,'\'')),
    
      // (A) Unterminated block comment: highlight opener, add EOF frame
      Map.entry(BadUnclosedBlockComment, (_, t, tz) -> {
        var file = tz.fileName();
        Span s= t.span(file);
        int lineEnd= t.content().indexOf('\n');
        if (lineEnd != -1){ s = new Span(file,s.startLine(),s.startCol(),s.startLine(),s.startCol()+lineEnd); }
        throw Code.UnexpectedToken
          .of("Unterminated block comment. Add \"*/\" to close it.")
          .addSpan(s);
      }),
      Map.entry(TokenKind.BadUnopenedBlockCommentClose, this::strayBlockCommentCloser),
      str(BadOpLine,"""
A "|" immediately before a quote starts a line string (e.g. `|"abc"` or `|'abc'`).
Operators can also contain "|", making it ambiguous what, for example, `<--|'foo'` means.
It could be the "<--" operator followed by `|'foo'` but also the "<--|" operator followed by `'foo'`. 
Please add spaces to disambiguate:  `<--| 'foo'`   or   `<-- |'foo'`
"""),     
      str(BadOpDigit,"""
An operator followed by a digit is parsed as a signed number (e.g. "+5", "-3").
Operators can also contain "+" and "-", making it ambiguous what, for example, "<--5" means.
It could be the "<--" operator followed by "5" but also the "<-" operator followed by "-5".
Please add spaces to disambiguate:  "<-- 5"   or   "<- -5"
"""),
      str(BadOSquare,"""
Here we expect "[" as a generic/RC argument opener and must follow the name with no space.
Write "Foo[Bar]" not "Foo [Bar]".
Write "x.foo[read]" not "x.foo [read]".
"""),
      str(BadFloat,"""
Float literals must have a sign and digits on both sides of ".".
Examples: "+1.0", "-0.5", "+12.0e-3".
Fearless does not allow float literals of form "1.2" or ".2".
"""), 
      str(BadRational,"""
Rational literals must have a sign.
Examples: "+1/2", "-3/4".
Fearless does not allow rational literals of form "1/2"
""")
    );
  }
  private Map.Entry<TokenKind, TokenProcessor<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>> str(TokenKind tk, String s){
    return Map.entry(tk, (_,t,tz) -> {
      String head= t.content().isBlank()
        ? "Unrecognized text."
        : "Unrecognized text " + Message.displayString(t.content()) + ".";

      throw Code.UnexpectedToken.of(head+"\n"+s).addSpan(t.span(tz.fileName())); 
      });
  }
  private Stream<Token> strayBlockCommentCloser(int idx, Token t, Tokenizer tokenizer){
    var file= tokenizer.fileName();
    var hit= findPseudoOpenerBefore(idx, tokenizer);
    var base= t.span(file);
    if (hit.isEmpty()){
      throw Code.UnexpectedToken
        .of("Unopened block comment close \"*/\". Remove it or add a matching \"/*\" before.")
        .addSpan(base);
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
     .addSpan(primary);
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
  private FearlessException errNoInfo(Span at, int quoteChar){ return Code.UnexpectedToken.of(errStart(quoteChar)).addSpan(at); }
  private FearlessException errEatAfter(Span at, int quoteChar){
    return Code.UnexpectedToken.of(errStart(quoteChar)
    + "A comment opening sign is present later on this line; did you mean to close the string before it?"
      ).addSpan(at); 
    }
  private FearlessException errEatBefore(Span at, int quoteChar){
    return Code.UnexpectedToken.of(errStart(quoteChar)
    + "A preceding block comment \"/* ... */\" on this line contains that quote.\n"
    + "Did it swallow the intended opening quote?"
      ).addSpan(at); 
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
    //If immediately before this token (ignoring whitespace) we have a BlockComment
    // that ENDS on THIS SAME LINE, and its *last line* contains this quoteChar,
    // then it probably swallowed the intended opening quote.
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
  @Override public FearlessException groupHalt(
      Token open, Token stop, Collection<TokenKind> expectedClosers, LikelyCause likely,
      Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, tokenizer, likely);

    var file= tokenizer.fileName();
    boolean sof= open.is(_SOF);
    boolean eof= stop.is(_EOF);
    boolean isCloser= stop.is(CRound, CSquare, CCurly, CCurlyId);
    boolean isBarrier= !eof && !isCloser;

    String openLabel= labelOf(open.kind());
    String stopLabel= eof ? "end of group" : labelOf(stop.kind());
    String base=
      sof
        ?"Unopened " + stopLabel + ".\n"
      :eof
        ? context() + openLabel + " group.\n"
      : isBarrier
        ? "Unclosed " + openLabel + " group before " + stopLabel + ".\n"
        : ("Wrong closer for " + openLabel + " group.\nFound instead: " + stopLabel + ".\n");
    String hint= switch (likely){
      case MissingCloser -> "Insert the expected closer before " + stopLabel + ".\n";
      case StrayCloser   -> "This "+stopLabel+" may be unintended.\n";
      case StrayOpener   -> "This "+openLabel+" may be unintended.\n";
      case MissingOpener -> "Insert the matching opener before this closer.\n";
      case Unknown       -> "";
    };
    var expected= sof?"":expected(hint.isEmpty()?"Expected ":"Otherwise expected ",expectedClosers);
    var span = eof ? open.span(file) : metaParser.Token.makeSpan(file, open, stop);
    var code= sof ? Code.Unopened : (eof || isBarrier) ? Code.Unclosed : Code.UnexpectedToken;
    return code.of(base + hint+ expected).addSpan(span);
  }
  @Override public FearlessException eatenCloserBetween(
      Token open, Token stop, Collection<TokenKind> expectedClosers,
      Token hiddenFragment, Token hiddenContainer, Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, hiddenFragment, hiddenContainer, tokenizer);

    var file= tokenizer.fileName();
    String where= describeFree(hiddenContainer);
    String msg=
      "Unclosed " + labelOf(open.kind()) + " group.\n"
    + "Found a matching closer inside a" + where + " between here and the stopping point.\n"
    + "Did you mean to place the closer outside the" + where + "?\n"
    + expected("Otherwise expected ",expectedClosers);
    var primary= metaParser.Token.makeSpan(file, open, hiddenFragment);
    var secondary= metaParser.Token.makeSpan(file, open, hiddenContainer);
    return Code.Unclosed.of(msg).addSpan(primary).addSpan(secondary);
  }
  @Override public FearlessException eatenOpenerBetween(
      Token open, Token stop, Collection<TokenKind> expectedClosers,
      Token hiddenFragment, Token hiddenContainer, Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, hiddenFragment, hiddenContainer, tokenizer);

    var file= tokenizer.fileName();
    String where= describeFree(hiddenContainer);
    String msg=
      "Unopened " + labelOf(stop.kind()) + ".\n"
    + "Found a matching opener hidden inside a" + where + " before this point.\n"
    + "Did you mean to place the opener outside the" + where + "?";
    var primary= metaParser.Token.makeSpan(file, hiddenFragment, stop);
    var secondary= metaParser.Token.makeSpan(file, hiddenContainer, stop);
    return Code.Unopened.of(msg).addSpan(primary).addSpan(secondary);
  }
  @Override public FearlessException runOfClosersBefore(
      Token open, Token stop, Collection<TokenKind> expectedClosers,
      List<Token> runOfClosers, Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, runOfClosers, tokenizer);
    assert !runOfClosers.isEmpty();

    var file= tokenizer.fileName();
    var k= runOfClosers.get(0).kind();
    String msg=
      "Unclosed " + labelOf(open.kind()) + " group.\n"
    + expected(expectedClosers)
    + "A contiguous run of " + labelOf(k) + " appears before this point; a closer may be missing earlier.";

    var runSpan= metaParser.Token.makeSpan(file, runOfClosers.get(0), runOfClosers.get(runOfClosers.size()-1));
    var primary= metaParser.Token.makeSpan(file, open, stop);
    return Code.Unclosed.of(msg).addSpan(runSpan).addSpan(primary);
  }
  @Override public FearlessException runOfOpenersBefore(
      Token open, Token badCloser, Collection<TokenKind> expectedClosers,
      List<Token> runOfOpeners, Tokenizer tokenizer){
    assert nonNull(open, badCloser, expectedClosers, runOfOpeners, tokenizer);
    assert !runOfOpeners.isEmpty();

    var file= tokenizer.fileName();
    var k= runOfOpeners.get(0).kind();
    String msg =
      "Unopened " + labelOf(badCloser.kind()) + ".\n"
    + "A contiguous run of " + labelOf(k) + " appears before this point; an opener may be missing earlier.";

    var pileSpan = metaParser.Token.makeSpan(file, runOfOpeners.get(0), runOfOpeners.get(runOfOpeners.size()-1));
    var primary  = metaParser.Token.makeSpan(file, runOfOpeners.get(0), badCloser);
    return Code.Unopened.of(msg).addSpan(pileSpan).addSpan(primary);
  }

  @Override public FearlessException missingButFound(
      Span at, String what, Token found, Collection<TokenKind> expectedTokens, Parser parser){
    assert nonNull(at, what, found, expectedTokens);
    String msg=
      "Missing " + (what.isBlank() ? "element" : what) + ".\n"
    + "Found instead: " + Message.displayString(found.content()) + ".\n"
    + expected(expectedTokens);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  public FearlessException badTopSelfName(Span at, String name){
    String msg= "Self name "+name+" invalid in a top level type.\n"
      + "Top level types self names can only be \"`this\".\n";
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
}