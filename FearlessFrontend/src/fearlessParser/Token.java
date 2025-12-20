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
  public static final TokenKind[] typeName= new TokenKind[]{UppercaseId,SignedFloat,SignedInt,UnsignedInt,SignedRational,SStr,UStr};
  public Token tokenFirstHalf(int length){
    assert length >= 0;
    assert tokens.isEmpty();
    assert content.length() >= length;
    return new Token(kind,content.substring(0, length),line,column,tokens);
  }
  public Token tokenSecondHalf(int length){
    assert length >= 0;
    if (length == 0){ return this; }
    assert tokens.isEmpty();
    assert content.length() >= length;
    Token first= tokenFirstHalf(length);
    Span s= first.span(Pos.unknown.fileName());
    return new Token(kind,content.substring(length),s.endLine(),s.endCol()+1,tokens);
  }
}
