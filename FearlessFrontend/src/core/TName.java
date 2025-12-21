package core;

import static fearlessParser.TokenKind.*;

import utils.Pos;

public record TName(String s, int arity, Pos pos){
  public TName{
    assert arity >= 0 : "arity < 0: "+arity;
    assert hasPkgDot(s) || validate(s,"TName", UppercaseId,UnsignedInt, SignedInt, SignedRational, SignedFloat, UStr, SStr);
  }
  static boolean hasPkgDot(String s){
    int i= s.indexOf('.');
    if (i == -1){ return false; }
    char c0= s.charAt(0);
    return c0 >= 'a' && c0 <= 'z';
  }
  static int pkgDot(String s){ return hasPkgDot(s) ? s.indexOf('.') : -1; }

  public TSpan approxSpan(){ return TSpan.fromPos(pos, simpleName().length()); }

  public TName withPkgName(String pkg){
    assert pkgName().isEmpty();
    return new TName(pkg+"."+s, arity, pos);
  }
  public TName withoutPkgName(){
    assert !pkgName().isEmpty();
    return new TName(simpleName(), arity, pos);
  }
  public TName withOverridePkgName(String pkg){
    return new TName(pkg+"."+simpleName(), arity, pos);
  }
  public TName withArity(int arity){ return new TName(s, arity, pos); }
  public String toString(){ return s+"/"+arity; }

  public String pkgName(){
    int i= pkgDot(s);
    return i == -1 ? "" : s.substring(0, i);
  }
  public String simpleName(){
    int i= pkgDot(s);
    return i == -1 ? s : s.substring(i + 1, s.length());
  }
  public static TName of(String name, int arity, Pos p){ return new TName(name, arity, p); }
}