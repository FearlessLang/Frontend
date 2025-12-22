package core;

import java.math.BigDecimal;
import java.math.BigInteger;
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
  static final BigInteger intMin= BigInteger.valueOf(Integer.MIN_VALUE);
  static final BigInteger intMax= BigInteger.valueOf(Integer.MAX_VALUE);
  static final BigInteger natMin= BigInteger.ZERO;
  static final BigInteger natMax= new BigInteger("4294967295"); // 2^32-1
  static String stripUnderscores(String s){ return s.replace("_",""); }
  static BigInteger big(String raw){ return new BigInteger(stripUnderscores(raw)); }
  static boolean inRange(BigInteger v, BigInteger min, BigInteger max){ return v.compareTo(min) >= 0 && v.compareTo(max) <= 0; }
  static public BigInteger intLiteralBig(String raw){ return big(raw); }
  static public boolean intLiteralInRange(String raw){ return inRange(intLiteralBig(raw),intMin,intMax); }
  static public BigInteger natLiteralBig(String raw){ return big(raw); }
  static public boolean natLiteralInRange(String raw){ return inRange(natLiteralBig(raw),natMin,natMax); }
  static int intLiteral32(String raw){
    BigInteger v= intLiteralBig(raw);
    assert inRange(v,intMin,intMax);
    return v.intValueExact();
  }
  static int natLiteralBits32(String raw){
    BigInteger v= natLiteralBig(raw);
    assert inRange(v,natMin,natMax);
    return v.intValue(); // wraps to low 32 bits (exactly what we want given the range)
  }
  static public BigDecimal floatLiteralBig(String raw){ return new BigDecimal(stripUnderscores(raw)); }
  static public boolean floatLiteralExactlyRepresentable(String raw){
    String ns= stripUnderscores(raw);
    if (ns.startsWith("+")){ ns = ns.substring(1); }
    BigDecimal dec= new BigDecimal(ns);     // exact decimal literal value
    double d= dec.doubleValue();            // rounded-to-double
    if (!Double.isFinite(d)){ return false; } // overflow -> Infinity
    return dec.compareTo(new BigDecimal(d)) == 0; // exact double value as decimal
  }
  public static String floatExactFearlessLit(double d){
    assert Double.isFinite(d);
    boolean neg= (Double.doubleToRawLongBits(d) & (1L<<63)) != 0;
    String mag= new BigDecimal(d).abs().toString(); // exact decimal for this double, may use E
    int e= mag.indexOf('E');
    if (e != -1){
      String base= mag.substring(0,e);
      String exp= mag.substring(e+1);
      if (base.indexOf('.') == -1){ base = base+".0"; }
      mag = base+"e"+exp;
    }
    else if (mag.indexOf('.') == -1){ mag = mag + ".0"; }
    return (neg ? "-" : "+") + mag;
  }
  static public double floatLiteralDouble(String raw){
    try { return Double.parseDouble(stripUnderscores(raw)); }
    catch(NumberFormatException ex){ return raw.startsWith("-") ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY; }
  }
  public static String toJavaLiteral(String s){
    if (s.startsWith("\"") || s.startsWith("`")){ return javaStrLit(s.substring(1,s.length()-1)); }
      String ns= stripUnderscores(s);
      if (TokenKind.isKind(ns,TokenKind.UnsignedInt)){
      // base.Nat: produce the signed int whose 32-bit pattern equals the unsigned value.
      // Later ops use: Integer.toUnsignedLong(x), compareUnsigned, divideUnsigned, etc.
      return Integer.toString(natLiteralBits32(ns));
      }
    if (TokenKind.isKind(ns,TokenKind.SignedInt)){ return Integer.toString(intLiteral32(ns)); }
    if (TokenKind.isKind(ns,TokenKind.SignedFloat)){
      assert floatLiteralExactlyRepresentable(ns);
      return Double.toString(floatLiteralDouble(ns))+"d";
    }
    if (TokenKind.isKind(ns,TokenKind.SignedRational)){
      int i= ns.indexOf('/');
      assert i != -1;
      String num= ns.substring(0,i), den= ns.substring(i+1);
      // TODO: make a proper Rational type
      return "new java.math.BigDecimal(\""+num+"\")"
        + ".divide(new java.math.BigDecimal(\""+den+"\"),java.math.MathContext.DECIMAL128)";
    }    
    throw Bug.unreachable();
  }
  static String javaStrLit(String raw){
    assert raw.indexOf('\n') == -1;
    var sb= new StringBuilder(raw.length()+2).append('"');
    for (int i= 0; i < raw.length(); i++){
      char c= raw.charAt(i);
      if (c == '\\' || c == '"'){ sb.append('\\'); }
      sb.append(c);
    }
    return sb.append('"').toString();
  }
}