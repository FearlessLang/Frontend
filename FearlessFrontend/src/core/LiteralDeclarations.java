package core;

import java.util.List;
import java.util.Map;

import core.E.Literal;
import fearlessParser.TokenKind;
import utils.Pos;
import utils.Bug;


public class LiteralDeclarations {
  public static TName baseSStr= new TName("base.SStr",0,Pos.unknown);
  public static TName baseUStr= new TName("base.UStr",0,Pos.unknown);
  public static TName baseNat= new TName("base.Nat",0,Pos.unknown);
  public static TName baseInt= new TName("base.Int",0,Pos.unknown);
  public static TName baseNum= new TName("base.Num",0,Pos.unknown);
  public static TName baseFloat= new TName("base.Float",0,Pos.unknown);
  public static TName widen= new TName("base.WidenTo",1,Pos.unknown);
  public static boolean isPrimitiveLiteral(String name){ return "+-1234567890\"`".contains(name.substring(0,1)); }
  static private core.E.Literal of(TName name,TName lit){
    var c= new T.C(lit,List.of());
    var self= new T.RCC(RC.imm,c,name.approxSpan());
    var w= new T.C(widen,List.of(self));
    return new core.E.Literal(RC.imm,name,List.of(),List.of(c,w),"this",List.of(),Src.syntetic,true);
  }
  public static core.E.Literal _from(TName n, Map<TName,Literal> map, OtherPackages other){
    var res= map.get(n);
    if (res == null){ res = other.of(n); }
    if (res != null){ return res; }
    if (!n.pkgName().equals("base") || !isPrimitiveLiteral(n.simpleName())){ return null; }
    return LiteralDeclarations.from(n);
  }
  public static core.E.Literal from(TName name){ return of(name,superLiteral(name)); }
  public static TName superLiteral(TName name){
    assert name.pkgName().equals("base");
    String s= name.simpleName();
    if (s.startsWith("`")){  return baseSStr; }
    if (s.startsWith("\"")){ return baseUStr; }
    if (TokenKind.isKind(s,TokenKind.UnsignedInt)){ return baseNat; }
    if (TokenKind.isKind(s,TokenKind.SignedInt)){ return baseInt; }
    if (TokenKind.isKind(s,TokenKind.SignedFloat)){ return baseFloat; }
    if (TokenKind.isKind(s,TokenKind.SignedRational)){ return baseNum; }    
    throw Bug.unreachable();
  }
}