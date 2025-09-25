package fearlessParser;

import java.util.*;

import message.Code;
import message.FearlessException;

public final class ParserErrors {
  private ParserErrors(){}
  
  public static Optional<String> suggest(String bad, Collection<String> pool){
    int best= Integer.MAX_VALUE;
    String pick= null;
    for (var s: pool){
      int d = dist(bad, s);
      if (d < best){ best = d; pick = s; }
    }
    return (pick!=null && best <= Math.max(1, bad.length()/3)) ? Optional.of(pick) : Optional.empty();
  }
  private static int dist(String a, String b){
    int n= a.length();
    int m= b.length();
    int[][] dp= new int[n+1][m+1];
    for(int i= 0; i <= n; i++){ dp[i][0]=i; }
    for(int j= 0; j <= m; j++){ dp[0][j]=j; }
    for(int i= 1; i <= n; i++){
      for(int j=1;j<=m;j++){
        int c= (a.charAt(i - 1) == b.charAt(j - 1) ? 0 : 1);
        dp[i][j] = Math.min(Math.min(dp[i-1][j]+1, dp[i][j-1]+1), dp[i-1][j-1]+c);
      }
    }
    return dp[n][m];
  }
/*  public static FearlessException unexpected(Token t, TokenKind... expected){
    String human = "Unexpected token "+tk(t)+(expected.length==0? "" : ". "+showExpected(expected));
    return Code.UnexpectedToken.of(t, human);
  }*/
  public static FearlessException disallowedReadHMutH(Token t){
    return Code.UnexpectedToken.of("""
      Capabilities readH and mutH are not allowed on closures
      Use one of read, mut, imm, iso""");
  }
  public static FearlessException nameNotInScope(Token idTok, Collection<String> inScope){
    return Code.UnexpectedToken.of(()->{
      String name= idTok.content();
      var maybe= suggest(name, inScope);
      var scope= inScope.isEmpty()
        ?"No names are in scope here.\n"
        :"In scope: "+String.join(", ", inScope)+"\n";
      return "Name `"+name+"` is not in scope\n"+scope
       +maybe.map(s->"did you mean `"+s+"` ?").orElse("");
      });
  }
  public static FearlessException nameRedeclared(String c){
    return Code.UnexpectedToken.of("Name `"+c+"` already in scope");
  }
  public static FearlessException typeNameConflictsGeneric(String name){
    return Code.UnexpectedToken.of("Type name `"+name+"` conflicts with a generic parameter in scope");
  }
  public static FearlessException missingExprAfterEq(){
    return Code.UnexpectedToken.of("""
      Missing expression after `=` in continuation-passing sugar
      Use: `.m x = expr` or `.m {a,b}= expr`
      The variable(s) are only in scope for the remaining posts of this call chain.
      """);
  }
/*  public static FearlessException rcOnlyCallSquareNeedsNoComma(){
    return Code.UnexpectedToken.of("After `[RC]` you may omit the comma if there are no type arguments");
  }*/
  public static FearlessException parameterNameExpected(){
    return Code.UnexpectedToken.of("Parameter name expected");
  }
  public static FearlessException spaceBeforeId(){
    return Code.UnexpectedToken.of("no space between closed curly and destruct id");
  }
  public static FearlessException badBound(String name){
    return Code.UnexpectedToken.of("Invalid bound for generic "+name+"""
      Only '*' or '**' are allowed here
      Write: X:*   // inferred mut,read,imm
         or: X:**  // inferred everything"
      """);}
  
  public static FearlessException genericNotInScope(String c, Collection<String> Xs){
    return Code.UnexpectedToken.of(()->
      "Generic type `"+c+"` is not in scope\n"
      + (Xs.isEmpty()
      ?"No generic parameters are declared here."
      :"Declared generics: "+String.join(", ", Xs)));
  }
}