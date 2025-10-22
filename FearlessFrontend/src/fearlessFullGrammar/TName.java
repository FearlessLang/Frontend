package fearlessFullGrammar;

import static fearlessParser.TokenKind.SStr;
import static fearlessParser.TokenKind.SignedFloat;
import static fearlessParser.TokenKind.SignedInt;
import static fearlessParser.TokenKind.SignedRational;
import static fearlessParser.TokenKind.UStr;
import static fearlessParser.TokenKind.UnsignedInt;
import static fearlessParser.TokenKind.UppercaseId;
import static fearlessParser.TokenKind.validate;

import fearlessParser.ClassicDecoder;
import fearlessParser.StringInfo;
import files.Pos;
import metaParser.Message;

public record TName(String s, int arity,String asStrLit,Pos pos){
  public TName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert s.indexOf(".") != -1 || validate(s,"TName", UppercaseId,UnsignedInt, SignedInt, SignedRational, SignedFloat, UStr, SStr);
  }
  public TName withPkgName(String pkg){
    assert pkgName().isEmpty();
    return new TName(pkg+"."+s,arity,asStrLit,pos);
  }
  public TName withOverridePkgName(String pkg){
    return new TName(pkg+"."+simpleName(),arity,asStrLit,pos);
  }

  public TName withArity(int arity){ return new TName(s,arity,asStrLit,pos); }
  public String toString(){
    if(asStrLit.isEmpty()){ return s+"/"+arity;}
    return s+"/"+arity+":"+Message.displayString(asStrLit);
  }
  public String pkgName(){
    int i= s.indexOf(".");
    return i == -1 ? "" : s.substring(0, i);
  }
  public String simpleName(){
    int i= s.indexOf(".");
    return i == -1 ? s : s.substring(i + 1, s.length());
  }
  public static TName of(String name, int arity, Pos p, StringInfo.RangeMsg err){
    String s= "";
    if(name.startsWith("\"")){ s = new ClassicDecoder(name.substring(1, name.length()-1), 0, err).of(); }
    if(name.startsWith("'")){ s = name.substring(1, name.length()-1); }//TODO: what about \n etc?
    return new TName(name,arity,s,p);
  }
}