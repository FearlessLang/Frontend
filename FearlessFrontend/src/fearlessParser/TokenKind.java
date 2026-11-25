package fearlessParser;

import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;

import metaParser.TokenMatch;

public enum TokenKind implements metaParser.TokenKind{
  Ws("\\s+", "white space or new line"),
  LineComment("//[^\\n]*", "line comment"),
  BlockComment("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/", "block comment"),
  BadUnclosedBlockComment("(?s)/\\*(?!.*?\\*/).*"),
  BadUnopenedBlockCommentClose("\\*/"),

  Arrow("->"),
  ORound("\\(", "\"(\""),
  CRound("\\)", "\")\""),
  OCurly("\\{", "\"{\""),
  CCurlyId("\\}[A-Za-z0-9_]+'*", "\"}\""),
  CCurly("\\}", "\"}\""),
  OSquareArg("(?<=[A-Za-z0-9_'`\\x22\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])(?<!\\x2A/)\\[", "\"[\""),//correctly not working for preceding literals
  BadOSquare("\\["),
  CSquare("\\]", "\"]\""),
  Underscore("_", "\"_\""),
  Comma(","),
  SemiColon(";"),
  ColonColon("::"),
  Colon(":"),
  Eq("="),
  SQuote("'"),
  ReadImm("read/imm"),//note: must be before read
  RCap("readH|mutH|imm|iso|read|mut", "reference capability"),

  // Signed float: +12.34, -1.0e-3 ; requires at least one digit on each side of '.'
  SignedFloat(
    "[+-](?:[0-9](?:[0-9_]*[0-9])?)\\.(?:[0-9](?:[0-9_]*[0-9])?)"
    +"(?:[eE][+-]?[0-9](?:[0-9_]*[0-9])?)?(?:soft)?", typeNameLabel()),
  UnSignedFloat(
    "[0-9](?:[0-9_]*[0-9])?\\x2E(?:[0-9](?:[0-9_]*[0-9])?)"
    +"(?:[eE][\\x2B\\x2D]?[0-9](?:[0-9_]*[0-9])?)?(?:soft)?", typeNameLabel()),
  // Signed int: +45, -10, +1_000
  SignedInt("[+-][0-9](?:[0-9_]*[0-9])?", typeNameLabel()),
  // Unsigned int: 0, 42, 1_000_000
  UnsignedInt("[0-9](?:[0-9_]*[0-9])?", typeNameLabel()),
  BadUStrUnclosed("\\x22[^\\x22\\x0A]*(?=\\x0A|\\z)"),
  BadSStrUnclosed("`[^`\\x0A]*(?=\\x0A|\\z)"),
  UStr("\\x22[^\\x22\\x0A]*\\x22", typeNameLabel()),
  SStr("`[^`\\x0A]*`", typeNameLabel()),
  DotName("\\._*[a-z][A-Za-z0-9_]*'*", methodNameLabel()),
  BadDotName("\\._*[A-Z][A-Za-z0-9_]*'*"),
  BadDot("\\.(?=\\s)"),
  BadChar("[@$]"),
  UppercaseId("(?:"+core.TName.pkgNameRegex+"\\x2E)?_*[A-Z][A-Za-z0-9_]*'*", typeNameLabel()),//correctly allows only one '.' since packages are not nested inside each others
  LowercaseId("_*[a-z][A-Za-z0-9_]*'*", "parameter name"),
  BadSStrQuote("'(?:(?!//|/\\x2A)[^'\\x0A\\x22`])*'(?![_a-z])"),
   //\  /  #  *   -   +   %  <  >  =  !  &   ^   ~   ?     |
  //[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F:\\x7C#]
  //forbid:  /*   */   //
  //(?!/\\x2A|\\x2A/|//)
  Op        ( "(?:(?!/\\x2A|\\x2A/|//)[\\x5C/#\\x2A\\x2D\\x2B%<>=!&\\x5E~\\x3F\\x7C])+", methodNameLabel()),
  // tokens that are never considered for matching, but useful for asserts and for labelling special cases
  _XId("_*[A-Z][A-Za-z0-9_]*'*", "type name"),
  _X("_*[A-Z][A-Za-z0-9_]*'*", "generic type parameter (like \"T\", \"E\", \"Key\").\nOr: generic type parameter with bounds (like \"T:*\", \"E: **\", \"Key: imm,mut\")"),
  _pkgName(core.TName.pkgNameRegex,//"[a-z][a-z0-9_]*"
    "id starting with a-z followed by any amount of a-z0-9 or the _ symbol"),
  _folderName("_"+core.TName.pkgNameRegex, "folder name: the _ symbol followed by a package name"),
  _use("use"),
  _map("map"),
  _as("as"),
  _in("in"),
  _instead("instead"),
  _of("of"),
  _EOF("", "end of file"),
  _SOF("", "start of file"),
  _All("", "full file"),
  _CurlyGroup("", "group in {..}"),
  _SquareGroup("", "group in [..]"),
  _RoundGroup("", "group in (..)");

  private final TokenMatch match;
  public final String human;

  TokenKind(String regex){ this(regex, "\""+regex+"\""); }
  TokenKind(String regex, String human){
    this.match= TokenMatch.fromRegex(regex);
    this.human= human;
  }
  private static String typeNameLabel(){ return "type name (like \"Point\", \"base.Nat\", \"12\", \"-3.5\", `\"abc\"`)"; }
  private static String methodNameLabel(){ return "method name (like \".foo\", \"+\", \"*\", \"-\")"; }
  @Override public TokenMatch matcher(){ return match; }
  public boolean synthetic(){ return name().startsWith("_"); }
  @Override public int priority(){ return ordinal(); }

  public static boolean validate(String input, String what, TokenKind... kinds){
    if (isKind(input, kinds)){ return true; }
    throw new IllegalArgumentException("["+input+"] is not a valid "+what);
  }
  public static boolean isKind(String input, TokenKind... kinds){
    Objects.requireNonNull(input);
    return Stream.of(kinds).anyMatch(k -> k.matcher().apply(input, 0).equals(Optional.of(input)));
  }
}