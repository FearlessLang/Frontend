package message;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessParser.RC;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import metaParser.ErrFactory;
import metaParser.Span;
import static offensiveUtils.Require.*;

public final class FearlessErrFactory implements ErrFactory<FearlessException,TokenKind>{
  private static String maybe(String prefix, boolean cond, String tail){ return cond ? prefix + tail : ""; }
  private static String joinOrEmpty(Collection<? extends Object> items){
    return items.isEmpty() ? "" : items.stream().map(Object::toString).collect(Collectors.joining(", "));
  }
  @Override public FearlessException illegalCharIn(int line, int col, String what){
    String msg= what.isBlank()
      ? "Illegal character at line=" + line + ", col=" + col
      : "Illegal character in " + what + " at line=" + line + ", col=" + col;
    return Code.UnexpectedToken.of(msg);
  }
  @Override public FearlessException unrecognizedTextAt(int line, int col, String what){
    String msg= what.isBlank()
      ? "Unrecognized text at line=" + line + ", col=" + col
      : "Unrecognized text in " + what + " at line=" + line + ", col=" + col;
    return Code.UnexpectedToken.of(msg);
  }
  @Override public FearlessException unclosedIn(String what, Span openedAt, Collection<TokenKind> expectedClosers){
    assert nonNull(what,openedAt,expectedClosers);
    String exp= joinOrEmpty(expectedClosers);
    String msg= "Unclosed " + what + " opened at " + openedAt
      + maybe(". Expected one of: ", !exp.isEmpty(), exp);
    return Code.Unclosed.of(msg);
  }
  @Override public FearlessException unopenedIn(String groupLabel, Span closerAt){
    assert nonNull(groupLabel,closerAt);
    String msg= "Unopened " + groupLabel + " closed at " + closerAt;
    return Code.Unopened.of(msg);
  }
  @Override public FearlessException missing(Span after, String what, List<TokenKind> expectedLabels){
    assert nonNull(after,what,expectedLabels);
    String exp= joinOrEmpty(expectedLabels);
    String msg= "Missing " + (what.isBlank() ? "element" : what)
      + " after " + after
      + maybe(". Expected: ", !exp.isEmpty(), exp);
    return Code.UnexpectedToken.of(msg);
  }
  @Override public FearlessException missingButFound(Span at, String what, String found, Collection<TokenKind> expectedLabels){
    assert nonNull(at,what,expectedLabels);
    String exp= joinOrEmpty(expectedLabels);
    String msg= "Missing " + (what.isBlank() ? "element" : what)
      +" at " + at+". Found instead: "+ found
      + maybe(". But that is not one of : ", expectedLabels.isEmpty(), exp);
    return Code.UnexpectedToken.of(msg);
  }
  @Override public FearlessException extraContent(Span from){
    assert nonNull(from);
    String msg= "Extra content in " + from;
    return Code.ExtraTokenInGroup.of(msg);
  }

  @Override public FearlessException probeStalledIn(String groupLabel, String probeName, int startIdx, int endIdx){
    String msg= "Probe " + probeName + " stalled while scanning " + groupLabel
      + " at [" + startIdx + ".." + endIdx + "]";
    return Code.ProbeError.of(msg);
  }

  @Override public FearlessException badProbeDropIn(String groupLabel, String probeName, int startIdx, int endIdx, int drop){
    String msg= "Probe " + probeName + " returned invalid drop=" + drop
      + " in " + groupLabel + " at [" + startIdx + ".." + endIdx + "]";
    return Code.ProbeError.of(msg);
  }
  public FearlessException disallowedReadHMutH(RC rc){
    return Code.UnexpectedToken.of(
      "Capability "+rc+"""
      used.
      Capabilities readH and mutH are not allowed on closures
      Use one of read, mut, imm, iso.      
      """);
  }
  public FearlessException nameNotInScope(Token name, Collection<String> inScope){
    return Code.UnexpectedToken.of(() -> {
      var maybe= suggest(name.content(), inScope);
      var scope= inScope.isEmpty()
        ? "No names are in scope here.\n"
        : "In scope: " + String.join(", ", inScope) + "\n";
      return "Name `"+name.content()+"` is not in scope\n" + scope
        + maybe.map(s -> "did you mean `"+s+"` ?").orElse("");
    });
  }
  public FearlessException nameRedeclared(String c){
    return Code.UnexpectedToken.of("Name `"+c+"` already in scope");
  }
  public FearlessException typeNameConflictsGeneric(String name){
    return Code.UnexpectedToken.of("Type name `"+name+"` conflicts with a generic parameter in scope");
  }
  public FearlessException missingExprAfterEq(){
    return Code.UnexpectedToken.of("""
      Missing expression after `=` in continuation-passing sugar
      Use: `.m x = expr` or `.m {a,b}= expr`
      The variable(s) are only in scope for the remaining posts of this call chain.
      """);
  }
  public FearlessException parameterNameExpected(){
    return Code.UnexpectedToken.of("Parameter name expected");
  }
  public FearlessException spaceBeforeId(){
    return Code.UnexpectedToken.of("no space between closed curly and destruct id");
  }
  public FearlessException badBound(String name){
    return Code.UnexpectedToken.of("Invalid bound for generic "+name+"""
      Only '*' or '**' are allowed here
      Write: X:*   // inferred mut,read,imm
         or: X:**  // inferred everything"
      """);
  }
  public FearlessException genericNotInScope(String X, Collection<String> Xs){
    return Code.UnexpectedToken.of(() ->
      "Generic type `"+X+"` is not in scope\n" +
      (Xs.isEmpty()
        ? "No generic parameters are declared here."
        : "Declared generics: " + String.join(", ", Xs)));
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