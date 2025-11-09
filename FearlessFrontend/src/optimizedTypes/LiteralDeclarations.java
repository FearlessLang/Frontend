package optimizedTypes;

import java.util.List;

import fearlessFullGrammar.TName;
import fearlessParser.TokenKind;
import files.Pos;
import fullWellFormedness.OtherPackages;
import inferenceGrammarB.Declaration;
import inferenceGrammarB.T;
import utils.Bug;


public class LiteralDeclarations {
  public static TName baseSStr= new TName("base.SStr",0,Pos.UNKNOWN);
  public static TName baseUStr= new TName("base.UStr",0,Pos.UNKNOWN);
  public static TName baseNat= new TName("base.Nat",0,Pos.UNKNOWN);
  public static TName baseInt= new TName("base.Int",0,Pos.UNKNOWN);
  public static TName baseNum= new TName("base.Num",0,Pos.UNKNOWN);
  public static TName baseFloat= new TName("base.Float",0,Pos.UNKNOWN);
  static private Declaration of(TName name,TName lit){ 
    return new Declaration(name,List.of(),List.of(new T.C(lit,List.of())),"this",List.of(),Pos.UNKNOWN);
  }
  public static Declaration from(TName name, OtherPackages other){
    assert name.pkgName().equals("base");
    String s= name.simpleName();
    if (s.startsWith("`")){  return of(name,baseSStr); }
    if (s.startsWith("\"")){ return of(name,baseUStr); }
    if (TokenKind.validate(s,TokenKind.UnsignedInt)){ return of(name,baseNat); }
    if (TokenKind.validate(s,TokenKind.SignedInt)){ return of(name,baseInt); }
    if (TokenKind.validate(s,TokenKind.SignedFloat)){ return of(name,baseFloat); }
    if (TokenKind.validate(s,TokenKind.SignedRational)){ return of(name,baseNum); }    
    throw Bug.unreachable();

  }
}
