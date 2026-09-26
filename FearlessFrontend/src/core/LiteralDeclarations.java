package core;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

import core.E.Literal;
import fearlessParser.TokenKind;
import utils.Pos;
import utils.Push;
import utils.Bug;


public final class LiteralDeclarations{
  private LiteralDeclarations(){}
  public static final TName baseStr= new TName("base.Str",0,Pos.unknown);
  public static final TName baseNat= new TName("base.Nat",0,Pos.unknown);
  public static final TName baseInt= new TName("base.Int",0,Pos.unknown);
  public static final TName baseFloat= new TName("base.Float",0,Pos.unknown);
  public static final TName widen= new TName("base.WidenTo",1,Pos.unknown);
  public static final TName sealed= new TName("base.Sealed",0,Pos.unknown);
  public static final TName captureFree= new TName("base.CaptureFree",0,Pos.unknown);
  public static final TName baseId= new TName("base.BaseId",2,Pos.unknown);
  public static final TName baseContainer= new TName("base.BaseContainer",1,Pos.unknown);
  public static final TName inferUnknown= new TName("base.InferUnknown",0,Pos.unknown);
  public static final List<TName> inferErrs= List.of(new TName("base.InferErr",2,Pos.unknown),new TName("base.InferErr",3,Pos.unknown),new TName("base.InferErr",4,Pos.unknown));
  public static boolean has(List<T.C> cs, TName magic){ return cs.stream().anyMatch(c->c.name().equals(magic)); }
  public static boolean isPrimitiveLiteral(String name){ return "+-1234567890\"`".contains(name.substring(0,1)); }
  private static core.E.Literal forge(TName name, Function<TName,Literal> map, OtherPackages other){
    var lit= superLiteral(name);
    var res= from(lit,map,other);
    var ms= res.ms().stream().map(m->m.withSig(m.sig().implementedBy(name))).toList();
    return new core.E.Literal(RC.imm,name,List.of(),Push.of(new T.C(lit,List.of()),res.cs()),"this",ms,Src.syntetic,true);
  }
  public static core.E.Literal from(TName n, Function<TName,Literal> map, OtherPackages other){ return Objects.requireNonNull(_from(n,map,other)); }
  public static core.E.Literal _from(TName n, Function<TName,Literal> map, OtherPackages other){
    var res= map.apply(n);
    if (res == null){ res= other.__of(n); }
    if (res != null){ return res; }
    var lit= n.pkgName().equals("base") && isPrimitiveLiteral(n.simpleName());
    if (!lit){ return null; }
    return forge(n,map,other);
  }
  public static TName superLiteral(TName name){
    assert name.pkgName().equals("base");
    var s= name.simpleName();
    var strLit= s.startsWith("`") || s.startsWith("\"");
    if (strLit){ return baseStr; }
    if (TokenKind.isKind(s,TokenKind.UnsignedInt)){ return baseNat; }
    if (TokenKind.isKind(s,TokenKind.SignedInt)){ return baseInt; }
    if (TokenKind.isKind(s,TokenKind.SignedFloat,TokenKind.UnSignedFloat)){ return baseFloat; }
    throw Bug.unreachable();
  }
  public static final BigInteger intMin= BigInteger.valueOf(Long.MIN_VALUE);
  public static final BigInteger intMax= BigInteger.valueOf(Long.MAX_VALUE);
  public static final BigInteger natMin= BigInteger.ZERO;
  public static final BigInteger natMax= new BigInteger(Long.toUnsignedString(-1L)); // 2^64-1

  public static final String softSuffix= "soft";
  static String stripUnderscores(String s){ return s.replace("_",""); }
  static String floatPayload(String raw){ return stripUnderscores(raw.endsWith(softSuffix) ? raw.substring(0,raw.length()-softSuffix.length()) : raw); }
  public static BigInteger big(String raw){ return new BigInteger(stripUnderscores(raw)); }
  static boolean inRange(BigInteger v, BigInteger min, BigInteger max){ return v.compareTo(min) >= 0 && v.compareTo(max) <= 0; }
  public static boolean intLiteralInRange(String raw){ return inRange(big(raw),intMin,intMax); }
  public static boolean natLiteralInRange(String raw){ return inRange(big(raw),natMin,natMax); }
  static long intLiteral64(String raw){
    var v= big(raw);
    assert inRange(v,intMin,intMax);
    return v.longValueExact();
  }
  static long natLiteralBits64(String raw){
    var v= big(raw);
    assert inRange(v,natMin,natMax);
    return v.longValue(); // wraps to low 64 bits (exactly what we want given the range)
  }
  public static boolean floatLiteralExactlyRepresentable(String raw){
    var ns= floatPayload(raw);
    if (ns.startsWith("+")){ ns= ns.substring(1); }
    var d= Double.parseDouble(ns);
    if (!Double.isFinite(d)){ return false; } // overflow -> Infinity
    if (d == 0){ return new BigDecimal(ns.replaceAll("[eE].*","")).signum() == 0; }
    return new BigDecimal(ns).compareTo(new BigDecimal(d)) == 0; // exact double value as decimal
  }
  public static boolean floatLiteralOk(String raw){ return raw.endsWith(softSuffix) ? Double.isFinite(floatLiteralDouble(raw)) : floatLiteralExactlyRepresentable(raw); }
  public static String floatExactFearlessLit(double d){
    assert Double.isFinite(d);
    var neg= (Double.doubleToRawLongBits(d) & (1L<<63)) != 0;
    var mag= new BigDecimal(d).abs().toString(); // exact decimal for this double, may use E
    var sign= neg ? "-" : "+";
    var e= mag.indexOf('E');
    if (e != -1){ return sign+mag.substring(0,e)+"e"+mag.substring(e+1); }
    if (!mag.contains(".")){ mag= mag + ".0"; }
    return sign+mag;
  }
  public static double floatLiteralDouble(String raw){
    try{ return Double.parseDouble(floatPayload(raw)); }
    catch(NumberFormatException ex){ return raw.startsWith("-") ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY; }
  }
  public static String toJavaLiteral(String s){
    var strLit= s.startsWith("`") || s.startsWith("\"");
    if (strLit){ return javaStrLit(s.substring(1,s.length()-1)); }
    var ns= stripUnderscores(s);
    if (TokenKind.isKind(ns,TokenKind.UnsignedInt)){
      // base.Nat: produce the signed int whose 64-bit pattern equals the unsigned value.
      // Later ops use: Integer.toUnsignedLong(x), compareUnsigned, divideUnsigned, etc.
      return natLiteralBits64(ns) +"L";
    }
    if (TokenKind.isKind(ns,TokenKind.SignedInt)){ return intLiteral64(ns) +"L"; }
    if (TokenKind.isKind(ns,TokenKind.SignedFloat,TokenKind.UnSignedFloat)){
      assert floatLiteralOk(ns);
      return floatLiteralDouble(ns) +"d";
    }
    throw Bug.unreachable();
  }
  static String javaStrLit(String raw){
    assert !raw.contains("\n");
    return "\""+raw.replace("\\","\\\\").replace("\"","\\\"")+"\"";
  }
}