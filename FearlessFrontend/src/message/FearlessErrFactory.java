package message;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessParser.RC;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import metaParser.ErrFactory;
import metaParser.Frame;
import metaParser.Span;
import static offensiveUtils.Require.*;

public final class FearlessErrFactory implements ErrFactory<FearlessException,TokenKind>{
  private static String maybe(String prefix, boolean cond, String tail){ return cond ? prefix + tail : ""; }
  private static String joinOrEmpty(Collection<? extends Object> items){
    return items.isEmpty() ? "" : items.stream().map(Object::toString).collect(Collectors.joining(", "));
  }
  @Override public FearlessException illegalCharAt(Span at, String what){
    String head= what.isBlank()
      ? "Illegal character"
      : "Illegal character in " + what;
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  @Override public FearlessException unrecognizedTextAt(Span at, String what){
    String head= what.isBlank()
      ? "Unrecognized text"
      : "Unrecognized text in " + what;
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  @Override public FearlessException unclosedIn(String what, Span openedAt, Collection<TokenKind> expectedClosers){
    assert nonNull(what, openedAt, expectedClosers);
    String exp= joinOrEmpty(expectedClosers);
    String head= "Unclosed " + what;
    String msg= head + maybe(". Expected one of: ", !exp.isEmpty(), exp);
    return Code.Unclosed.of(msg).addSpan(openedAt);
  }
  @Override public FearlessException unopenedIn(String groupLabel, Span closerAt){
    assert nonNull(groupLabel, closerAt);
    String head= "Unopened " + groupLabel;
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
      +" at " + at+". Found instead: "+ found
      + maybe(". But that is not one of : ", !expectedLabels.isEmpty(), exp);
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
      var maybe= suggest(name.content(), inScope);
      var scope= inScope.isEmpty()
        ? "No names are in scope here.\n"
        : "In scope: " + String.join(", ", inScope) + "\n";
      return "Name `"+name.content()+"` is not in scope\n" + scope
        + maybe.map(s -> "did you mean `"+s+"` ?").orElse("");
    }).addSpan(at);
  }
  public FearlessException nameRedeclared(Token c, Span at){
    return Code.UnexpectedToken.of("Name `"+c.content()+"` already in scope").addSpan(at);
  }
  public FearlessException typeNameConflictsGeneric(Token name, Span at){
    return Code.UnexpectedToken.of("Type name `"+name.content()+"` conflicts with a generic parameter in scope").addSpan(at);
  }
  public FearlessException missingExprAfterEq(Span at){
    return Code.UnexpectedToken.of("""
      Missing expression after `=` in continuation-passing sugar
      Use: `.m x = expr` or `.m {a,b}= expr`
      The variable(s) are only in scope for the remaining posts of this call chain.
      """).addSpan(at);
  }
  public FearlessException parameterNameExpected(Span at){
    return Code.UnexpectedToken.of("Parameter name expected").addSpan(at);
  }
  public FearlessException spaceBeforeId(Span at){
    return Code.UnexpectedToken.of("no space between closed curly and destruct id").addSpan(at);
  }
  public FearlessException badBound(String name, Span at){
    return Code.UnexpectedToken.of("Invalid bound for generic "+name+"""
      Only '*' or '**' are allowed here
      Write: X:*   // inferred mut,read,imm
         or: X:**  // inferred everything"
      """).addSpan(at);
  }
  public FearlessException genericNotInScope(Token X, Span at, Collection<String> Xs){
    return Code.UnexpectedToken.of(() ->
      "Generic type `"+X.content()+"` is not in scope\n" +
      (Xs.isEmpty()
        ? "No generic parameters are declared here."
        : "Declared generics: " + String.join(", ", Xs))).addSpan(at);
  }
  private static Optional<String> suggest(String bad, Collection<String> pool){
    int best = Integer.MAX_VALUE;
    String pick = null;
    for (var s: pool){
      int d = dist(bad, s);
      if (d < best){ best = d; pick = s; }
    }
    return (pick != null && best <= Math.max(1, bad.length()/3))
      ? Optional.of(pick) : Optional.empty();
  }
  private static int dist(String a, String b){
    int n= a.length(), m= b.length();
    int[][] dp= new int[n+1][m+1];
    for(int i=0;i<=n;i++) dp[i][0]=i;
    for(int j=0;j<=m;j++) dp[0][j]=j;
    for(int i=1;i<=n;i++){
      for(int j=1;j<=m;j++){
        int c= (a.charAt(i-1)==b.charAt(j-1)?0:1);
        dp[i][j]=Math.min(Math.min(dp[i-1][j]+1, dp[i][j-1]+1), dp[i-1][j-1]+c);
      }
    }
    return dp[n][m];
  }
}