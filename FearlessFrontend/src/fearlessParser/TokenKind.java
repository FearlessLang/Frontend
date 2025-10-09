package fearlessParser;

import java.util.Objects;

import metaParser.TokenMatch;


public enum TokenKind implements metaParser.TokenKind {
  Ws("\\s+", true),
  LineComment("//[^\\n]*", true),
  BlockComment("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/", true),
  BadUnclosedBlockComment("(?s)/\\*(?!.*?\\*/).*"),
  BadUnopenedBlockCommentClose("\\*/"),
  
  UStrInterHash("#{1,}\\|\"[^\\n]*"),
  SStrInterHash("#{1,}\\|'[^\\n]*"),
  UStrLine("\\|\"[^\\n]*"),
  SStrLine("\\|'[^\\n]*"),

  Arrow("->"),
  ORound("\\("),
  CRound("\\)"),
  OCurly("\\{"),
  CCurlyId("\\}[A-Za-z0-9_]+`*"),
  CCurly("\\}"),
  OSquareArg("(?<=[A-Za-z0-9_`\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])\\["),//correctly not working for preceding literals
  BadOSquare("\\["),
  CSquare("\\]"),
  Comma(","),
  SemiColon(";"),
  ColonColon("::"),
  Colon(":"),
  Eq("="),
  BackTick("`"), 
  ReadImm("read/imm"),//note: must be before read
  RCap("readH|mutH|imm|iso|read|mut"),
  BadRational(
     "[0-9](?:[0-9_]*[0-9])?/[0-9](?:[0-9_]*[0-9])?"),
  SignedRational("[+-][0-9](?:[0-9_]*[0-9])?/[0-9](?:[0-9_]*[0-9])?"),

  BadFloat(
      "[0-9](?:[0-9_]*[0-9])?\\x2E(?:[0-9](?:[0-9_]*[0-9])?)"
     +"(?:[eE][\\x2B\\x2D]?[0-9](?:[0-9_]*[0-9])?)?"),
  // Signed float: +12.34, -1.0e-3 ; requires at least one digit on each side of '.'
  SignedFloat(
    "[+-](?:[0-9](?:[0-9_]*[0-9])?)\\.(?:[0-9](?:[0-9_]*[0-9])?)"
    + "(?:[eE][+-]?[0-9](?:[0-9_]*[0-9])?)?"),
  // Signed int: +45, -10, +1_000
  SignedInt("[+-][0-9](?:[0-9_]*[0-9])?"),
  // Unsigned int: 0, 42, 1_000_000
  UnsignedInt("[0-9](?:[0-9_]*[0-9])?"),
  BadUStrUnclosed("\\x22(?:\\x5C[ntu\\x22\\x5C]|[^\\x22\\x5C\\x0A])*(?=\\x0A|\\z)"),
  BadSStrUnclosed("'(?:\\x5C[nt'\\x5C]|[^'\\x5C\\x0A])*(?=\\x0A|\\z)"),
  // Normal strings with escapes; newlines not allowed inside
  //UStr("\"(?:\\\\.|[^\"\\\\\\r\\n])*\""),//broken
  //SStr("'(?:\\\\.|[^'\\\\\\r\\n])*'"),
  UStr("\\x22(?:\\x5C[ntu\\x22\\x5C]|[^\\x22\\x5C\\x0A])*\\x22"),
    // "(?:\[ntu"\]|[^"\\n])*"//we will need to handle \ u in post?
    //if we want no unicode in the source, how to handle |"  with no escapes?
    //solution: we allow{\ u...}, again, handled in post. (note, I can not write \ and u without space in valid java :-/
  SStr("'(?:\\x5C[nt'\\x5C]|[^'\\x5C\\x0A])*'"),

  DotName("\\._*[a-z][A-Za-z0-9_]*`*"),
  UppercaseId("(?:[a-z][a-z0-9_]*\\x2E)?_*[A-Z][A-Za-z0-9_]*`*"),//correctly allows only one '.' since packages are not nested inside each others  
  LowercaseId("_*[a-z][A-Za-z0-9_]*`*"),
   //\  /  #  *   -   +   %  <  >  =  !  &   ^   ~   ?     |
  //[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F:\\x7C#]
  //forbid:  /*   */   //
  //(?!/\\x2A|\\x2A/|//)
  BadOpDigit( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])*[\\x2B\\x2D](?=\\d)" ),
  BadOpLine ( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])*\\x7C(?=[\\x22'])" ),
  Op        ( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])+" ),
  //IMPORTANT: BadOp* must precede Op so bad forms win ties of equal length.
  // tokens that are never considered for matching, but useful for asserts and for labelling special cases  
  _XId("_*[A-Z][A-Za-z0-9_]*`*"),
  _pkgName("(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*"),   
  _package("package"),
  _role("role"),
  _roleName("(?:base|core|driver|worker|framework|accumulator|tool|app)[0-9][0-9][0-9]"),
  _use("use"),
  _map("map"),
  _as("as"),
  _EOF(""),
  _SOF(""),
  _All(""),
  _CurlyGroup(""),
  _SquareGroup(""),
  _RoundGroup(""); 

  private final String displayName;
  private final TokenMatch match;
  private final boolean hidden;

  TokenKind(String regex){ this(regex,false); }

  TokenKind(String regex, boolean hidden){
    this.displayName = name();
    this.match = TokenMatch.fromRegex(regex);
    this.hidden = hidden;
  }
  @Override public TokenMatch matcher(){ return match; }
  public boolean hidden(){ return hidden; }
  public boolean syntetic(){ return this.name().startsWith("_"); }
  public boolean bad(){ return this.name().startsWith("Bad"); }
  @Override public String toString(){ return displayName; }
  @Override public int priority(){ return this.ordinal(); }
  
  public static boolean validate(String input, String what, TokenKind... kinds){
    Objects.requireNonNull(input);
    Objects.requireNonNull(kinds);
    for (TokenKind k: kinds){
      var m= k.matcher().apply(input, 0);
      var all= m.isPresent() && m.get().length() == input.length();
      if (all){ return true; }
    }
    throw new IllegalArgumentException("["+input+"] is not a valid "+what);
  }
}