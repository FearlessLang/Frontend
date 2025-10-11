package fearlessFullGrammar;

import static fearlessParser.TokenKind.SStr;
import static fearlessParser.TokenKind.SignedFloat;
import static fearlessParser.TokenKind.SignedInt;
import static fearlessParser.TokenKind.SignedRational;
import static fearlessParser.TokenKind.UStr;
import static fearlessParser.TokenKind.UnsignedInt;
import static fearlessParser.TokenKind.UppercaseId;
import static fearlessParser.TokenKind.validate;

import metaParser.Message;

public record TName(String s, int arity,String asUStrLit){
  public TName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert validate(s,"TName", UppercaseId,UnsignedInt, SignedInt, SignedRational, SignedFloat, UStr, SStr);
  }
  public TName withArity(int arity){ return new TName(s,arity,asUStrLit); }
  public String toString(){
    if(asUStrLit.isEmpty()){ return s+"/"+arity;}
    return s+"/"+arity+":"+Message.displayString(asUStrLit);
  }
}