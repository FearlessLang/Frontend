package fearlessParser;

import java.util.Objects;

import metaParser.TokenMatch;


public enum TokenKind implements metaParser.TokenKind {
  Ws("\\s+", true," white space or new line"),
  LineComment("//[^\\n]*", true, "//.."),
  BlockComment("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/", true,"/*..*/"),
  BadUnclosedBlockComment("(?s)/\\*(?!.*?\\*/).*"),
  BadUnopenedBlockCommentClose("\\*/"),
  
  UStrInterHash("#{1,}\\|\"[^\\n]*","#|\"..."),
  SStrInterHash("#{1,}\\|`[^\\n]*","#|`..."),
  UStrLine("\\|\"[^\\n]*","|\"..."),
  SStrLine("\\|`[^\\n]*","|`..."),
  BadSStrLineQuote("\\|'[^\\n]*"),    
  Arrow("->"),
  ORound("\\(","("),
  CRound("\\)",")"),
  OCurly("\\{","{"),
  CCurlyId("\\}[A-Za-z0-9_]+'*","}id"),
  CCurly("\\}","}"),
  OSquareArg("(?<=[A-Za-z0-9_'\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])\\[","["),//correctly not working for preceding literals
  BadOSquare("\\["),
  CSquare("\\]","]"),
  Underscore("_","underscore"),
  Comma(","),
  SemiColon(";"),
  ColonColon("::"),
  Colon(":"),
  Eq("="),
  SQuote("'"), 
  ReadImm("read/imm"),//note: must be before read
  RCap("readH|mutH|imm|iso|read|mut","reference capability"),
  BadRational(
    "(?:[0-9](?:[0-9_]*[0-9])?(?:\\x2E[0-9](?:[0-9_]*[0-9])?)?)/(?:[0-9](?:[0-9_]*[0-9])?(?:\\x2E[0-9](?:[0-9_]*[0-9])?)?)"),
  SignedRational(
    "[+-](?:[0-9](?:[0-9_]*[0-9])?(?:\\x2E[0-9](?:[0-9_]*[0-9])?)?)/(?:[0-9](?:[0-9_]*[0-9])?(?:\\x2E[0-9](?:[0-9_]*[0-9])?)?)",
    "signed rational number (eg. +2.2/3.4)"),

  BadFloat(
    "[0-9](?:[0-9_]*[0-9])?\\x2E(?:[0-9](?:[0-9_]*[0-9])?)"
    +"(?:[eE][\\x2B\\x2D]?[0-9](?:[0-9_]*[0-9])?)?"),
  // Signed float: +12.34, -1.0e-3 ; requires at least one digit on each side of '.'
  SignedFloat(
    "[+-](?:[0-9](?:[0-9_]*[0-9])?)\\.(?:[0-9](?:[0-9_]*[0-9])?)"
    + "(?:[eE][+-]?[0-9](?:[0-9_]*[0-9])?)?","signed number (eg. -23.0045)"),
  // Signed int: +45, -10, +1_000
  SignedInt("[+-][0-9](?:[0-9_]*[0-9])?","signed number (eg. -23)"),
  // Unsigned int: 0, 42, 1_000_000
  UnsignedInt("[0-9](?:[0-9_]*[0-9])?","unsigned number (eg. 23)"),
  BadUStrUnclosed("\\x22[^\\x22\\x0A]*(?=\\x0A|\\z)"),
  BadSStrUnclosed("`[^`\\x0A]*(?=\\x0A|\\z)"),
  UStr("\\x22[^\\x22\\x0A]*\\x22","\"...\""),
  SStr("`[^`\\x0A]*`","`...`"),
  DotName("\\._*[a-z][A-Za-z0-9_]*'*",".name"),
  UppercaseId(
    "(?:(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*\\x2E)?_*[A-Z][A-Za-z0-9_]*'*",
    "type name"),//correctly allows only one '.' since packages are not nested inside each others  
  BadUppercaseId("(?:[a-z][a-z0-9_]*\\x2E)?_*[A-Z][A-Za-z0-9_]*'*"),
  LowercaseId("_*[a-z][A-Za-z0-9_]*'*","name"),
  BadSStrQuote("'[^'\\x0A]*'"),
   //\  /  #  *   -   +   %  <  >  =  !  &   ^   ~   ?     |
  //[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F:\\x7C#]
  //forbid:  /*   */   //
  //(?!/\\x2A|\\x2A/|//)
  BadOpDigit( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])*[\\x2B\\x2D](?=\\d)" ),
  BadOpLine ( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])*\\x7C(?=[\\x22`])" ),
  Op        ( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])+","binary operator (eg. +, *, -)"),
  //IMPORTANT: BadOp* must precede Op so bad forms win ties of equal length.
  // tokens that are never considered for matching, but useful for asserts and for labelling special cases  
  _XId("_*[A-Z][A-Za-z0-9_]*'*","type name"),
  _pkgName("(?!(?:con|prn|aux|nul)(?![a-z0-9_])|(?:com|lpt)[1-9](?![a-z0-9_]))[a-z][a-z0-9_]*",
    "id starting with a-z followed by any amount of a-z0-9 or the _ symbol"),   
  _package("package"),
  _role("role"),
  _roleName("(?:base|core|driver|worker|framework|accumulator|tool|app)[0-9][0-9][0-9]",
    " one of: base, core, driver, worker, framework, accumulator, tool, app "
    +"followed by rank (eg. core023, app000, framework999)"),
  _use("use"),
  _map("map"),
  _as("as"),
  _in("in"),
  _EOF("","end of file"),
  _SOF("","start of file"),
  _All("","full file"),
  _CurlyGroup("","group in {..}"),
  _SquareGroup("","group in [..]"),
  _RoundGroup("","group in (..)"); 

  private final String displayName;
  private final TokenMatch match;
  private final boolean hidden;
  public final String human;

  TokenKind(String regex){ this(regex,false,regex); }
  TokenKind(String regex, String human){ this(regex,false,human); }

  TokenKind(String regex, boolean hidden, String human){
    this.displayName = name();
    this.match = TokenMatch.fromRegex(regex);
    this.hidden = hidden;
    this.human = human;
  }
  @Override public TokenMatch matcher(){ return match; }
  public boolean hidden(){ return hidden; }
  public boolean syntetic(){ return this.name().startsWith("_"); }
  public boolean bad(){ return this.name().startsWith("Bad"); }
  @Override public String toString(){ return displayName; }
  @Override public int priority(){ return this.ordinal(); }
  
  public static boolean validate(String input, String what, TokenKind... kinds){
    if (isKind(input,kinds)){ return true; }
    throw new IllegalArgumentException("["+input+"] is not a valid "+what);
  }
  public static boolean isKind(String input, TokenKind... kinds){
    Objects.requireNonNull(input);
    Objects.requireNonNull(kinds);
    for (TokenKind k: kinds){
      var m= k.matcher().apply(input, 0);
      var all= m.isPresent() && m.get().length() == input.length();
      if (all){ return true; }
    }
    return false;
  }
}