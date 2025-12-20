package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import utils.Pos;

public record TName(String s, int arity,Pos pos){
  public TName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert s.indexOf(".") != -1 || validate(s,"TName", UppercaseId,UnsignedInt, SignedInt, SignedRational, SignedFloat, UStr, SStr);
  }
  public TSpan approxSpan(){ return TSpan.fromPos(pos,simpleName().length()); }
  public TName withPkgName(String pkg){
    assert pkgName().isEmpty();
    return new TName(pkg+"."+s,arity,pos);
  }
  public TName withoutPkgName(){
    assert !pkgName().isEmpty();
    return new TName(simpleName(),arity,pos);
  }
  public TName withOverridePkgName(String pkg){
    return new TName(pkg+"."+simpleName(),arity,pos);
  }

  public TName withArity(int arity){ return new TName(s,arity,pos); }
  public String toString(){ return s+"/"+arity; }
  public String pkgName(){
    int i= s.indexOf(".");
    return i == -1 ? "" : s.substring(0, i);
  }
  public String simpleName(){
    int i= s.indexOf(".");
    return i == -1 ? s : s.substring(i + 1, s.length());
  }
  public static TName of(String name, int arity, Pos p){
    return new TName(name,arity,p);
  }
}