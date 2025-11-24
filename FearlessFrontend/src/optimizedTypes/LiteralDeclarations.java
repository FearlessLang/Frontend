package optimizedTypes;

import java.util.List;

import fearlessFullGrammar.TName;
import fearlessParser.RC;
import fearlessParser.TokenKind;
import files.Pos;
import inferenceCore.Declaration;
import inferenceCore.T;
import pkgmerge.OtherPackages;
import utils.Bug;


public class LiteralDeclarations {
  public static TName baseSStr= new TName("base.SStr",0,Pos.UNKNOWN);
  public static TName baseUStr= new TName("base.UStr",0,Pos.UNKNOWN);
  public static TName baseNat= new TName("base.Nat",0,Pos.UNKNOWN);
  public static TName baseInt= new TName("base.Int",0,Pos.UNKNOWN);
  public static TName baseNum= new TName("base.Num",0,Pos.UNKNOWN);
  public static TName baseFloat= new TName("base.Float",0,Pos.UNKNOWN);
  public static TName widen= new TName("base.WidenTo",1,Pos.UNKNOWN);
  public static boolean isPrimitiveLiteral(String name){ return "+-1234567890\"`".contains(name.substring(0,1)); }
  static private Declaration of(TName name,TName lit){
    var c= new T.C(lit,List.of());
    var self= new T.RCC(RC.imm,c);
    var w= new T.C(widen,List.of(self));
    return new Declaration(name,List.of(),List.of(c,w),"this",List.of(),Pos.UNKNOWN);
  }
  public static Declaration from(TName name, OtherPackages other){
    assert name.pkgName().equals("base");
    String s= name.simpleName();
    if (s.startsWith("`")){  return of(name,baseSStr); }
    if (s.startsWith("\"")){ return of(name,baseUStr); }
    if (TokenKind.isKind(s,TokenKind.UnsignedInt)){ return of(name,baseNat); }
    if (TokenKind.isKind(s,TokenKind.SignedInt)){ return of(name,baseInt); }
    if (TokenKind.isKind(s,TokenKind.SignedFloat)){ return of(name,baseFloat); }
    if (TokenKind.isKind(s,TokenKind.SignedRational)){ return of(name,baseNum); }    
    throw Bug.unreachable();

  }
}
