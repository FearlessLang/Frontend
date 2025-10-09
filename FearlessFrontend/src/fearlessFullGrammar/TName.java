package fearlessFullGrammar;

import static fearlessParser.TokenKind.SStr;
import static fearlessParser.TokenKind.SignedFloat;
import static fearlessParser.TokenKind.SignedInt;
import static fearlessParser.TokenKind.SignedRational;
import static fearlessParser.TokenKind.UStr;
import static fearlessParser.TokenKind.UnsignedInt;
import static fearlessParser.TokenKind.UppercaseId;
import static fearlessParser.TokenKind.validate;

public record TName(String s, int arity){
  public TName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert validate(s,"TName", UppercaseId,UnsignedInt, SignedInt, SignedRational, SignedFloat, UStr, SStr);
  }
  public TName withArity(int arity){ return new TName(s,arity); }
}