package fearlessParser;

import static fearlessParser.TokenKind.Float;
import static fearlessParser.TokenKind.SStr;
import static fearlessParser.TokenKind.SignedInt;
import static fearlessParser.TokenKind.SignedRational;
import static fearlessParser.TokenKind.UStr;
import static fearlessParser.TokenKind.UnsignedInt;
import static fearlessParser.TokenKind.UpId;

import java.util.List;

public record Token(
  TokenKind kind, String content, int line, int column, List<Token> tokens
  ) implements metaParser.Token<Token,TokenKind>{
  public String toString(){return kind.name()+"|"+content;}
  boolean isTypeName(){ return is(typeName); }
  public static final TokenKind[] typeName= new TokenKind[]{UpId,Float,SignedInt,UnsignedInt,SignedRational,SStr,UStr};
}
