package message;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import fearlessParser.RC;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import metaParser.ErrFactory;
import metaParser.Frame;
import metaParser.Message;
import metaParser.NameSuggester;
import metaParser.Span;
import static offensiveUtils.Require.*;

public final class FearlessErrFactory implements ErrFactory<FearlessException,TokenKind>{
  private static String maybe(String prefix, boolean cond, String tail){ return cond ? prefix + tail : ""; }

  @Override public FearlessException illegalCharAt(Span at, int cp){
    String head= "Illegal character "+Message.displayChar(cp);
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  @Override public FearlessException unopenedIn(String what, Span closerAt){
    assert nonNull(what, closerAt);
    String head= "Unopened " + Message.displayString(what);
    return Code.Unopened.of(head).addSpan(closerAt);
  }
  @Override public FearlessException missing(Span at, String what, List<TokenKind> expectedLabels){
    assert nonNull(at,what,expectedLabels);
    String exp= joinOrEmpty(expectedLabels);
    String label= what.isBlank() ? "element" : what;
    String msg = "Missing " + label + maybe(". Expected: ", !exp.isEmpty(), exp);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  @Override public FearlessException missingButFound(Span at, String what, String found, Collection<TokenKind> expectedLabels){
    assert nonNull(at,what,expectedLabels);
    String exp= joinOrEmpty(expectedLabels);
    String msg= "Missing " + (what.isBlank() ? "element" : what)
      +".\nFound instead: "+ Message.displayString(found)+"."
      + maybe("\nBut that is not one of : ", !expectedLabels.isEmpty(), exp);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  @Override public FearlessException extraContent(Span from){
    assert nonNull(from);
    String msg= "Extra content in the current group";
    return Code.ExtraTokenInGroup.of(msg).addSpan(from);
  }
  @Override public FearlessException probeStalledIn(String groupLabel, Span at, int startIdx, int endIdx){
    String head= "Probe stalled while scanning " + groupLabel;
    return Code.ProbeError.of(head).addSpan(at);
  }
  @Override public FearlessException badProbeDropIn(String groupLabel, Span at, int startIdx, int endIdx, int drop){
    String msg= "Probe returned invalid drop=" + drop
      + " in " + groupLabel + " at [" + startIdx + ".." + endIdx + "]";
    return Code.ProbeError.of(msg).addSpan(at);
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
  @Override public FearlessException unclosedIn(String what, Span openedAt, Collection<TokenKind> expectedClosers){
    assert nonNull(what, openedAt, expectedClosers);
    String exp= joinOrEmpty(expectedClosers);
    String msg=
      "File ended while parsing " + Message.displayString(what) + "."
     + maybe("\nExpected one of: ", !exp.isEmpty(), exp);
    return Code.Unclosed.of(msg).addSpan(openedAt);
  }
  private static String joinOrEmpty(Collection<? extends Object> items){
    if (items.isEmpty()){ return ""; }
    return items.stream()
      .map(FearlessErrFactory::labelOf)
      .collect(Collectors.joining(", "));
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
  @Override public FearlessException unrecognizedTextAt(Span at, String what){
    String head= what.isBlank()
      ? "Unrecognized text."
      : "Unrecognized text " + Message.displayString(what)+".";
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  public FearlessException missingSemicolonOrOperator(Span at){
    return Code.MissingSeparator.of(
      "There is a missing \";\", operator or method name here or before").addFrame(new Frame("", at));
  }

  public FearlessException badTokenAt(Span at, TokenKind kind, String text){
    String head = text.isBlank()
      ? "Unrecognized text."
      : "Unrecognized text " + Message.displayString(text) + ".";

    String hint = switch (kind) {
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
"[" here is parsed as a generic/RC argument opener and must follow the name with no space.
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
}