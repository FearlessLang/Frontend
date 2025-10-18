package fearlessFullGrammar;

import static fearlessParser.TokenKind.DotName;
import static fearlessParser.TokenKind.Op;
import static fearlessParser.TokenKind.validate;

public record MName(String s, int arity){
  public MName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert validate(s,"MName", DotName, Op);
  }
  public MName withArity(int arity){ return new MName(s,arity); }
  public String toString(){ return s; }
}