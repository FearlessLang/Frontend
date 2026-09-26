package fearlessParser;

import static fearlessParser.TokenKind.*;

import java.util.List;

import utils.Pos;
import metaParser.Span;

public record Token(
  TokenKind kind, String content, int line, int column, List<Token> tokens
  ) implements metaParser.Token<Token,TokenKind>{
  public String toString(){return kind.name()+"|"+content;}
  boolean isTypeName(){ return is(typeName); }
  public static final TokenKind[] typeName= new TokenKind[]{UppercaseId,SignedFloat,UnSignedFloat,SignedInt,UnsignedInt,SStr,UStr};
  public Token tokenFirstHalf(int length){
    assert tokens.isEmpty();
    return new Token(kind,content.substring(0, length),line,column,tokens);
  }
  public Token tokenSecondHalf(int length){
    if (length == 0){ return this; }
    var first= tokenFirstHalf(length);
    var s= first.span(Pos.unknown.fileName());
    return new Token(kind,content.substring(length),s.endLine(),s.endCol()+1,tokens);
  }
}
