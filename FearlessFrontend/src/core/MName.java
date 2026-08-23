package core;

import static fearlessParser.TokenKind.*;

public record MName(String s, int arity){
  public MName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert validate(s,"MName", DotName, Op);
  }
  public MName withArity(int arity){ return new MName(s,arity); }
  public static boolean isMethodName(String s){ return isKind(s,DotName,Op); }
  public String toString(){ return s; }
}