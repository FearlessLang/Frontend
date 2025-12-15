package message;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import inference.IT;
import metaParser.Message;
import typeSystem.TypeScope;
import typeSystem.TypeSystem.*;
import utils.Bug;

final class Err{
  final StringBuilder sb= new StringBuilder();
  static Err of(){ return new Err(); }
  static String disp(Object o){ return Message.displayString(o.toString()); }
  static String typeDecName(TName name){ return disp(name.simpleName()+genArity(name.arity())); }
  static String typeDecNamePkg(TName name){ return disp(tNameDirect(name)); }
  static String tNameDirect(TName n){ return n.s()+genArity(n.arity()); }
  static boolean useImplName(Literal l){ return l.infName(); }
  static boolean useImplName(inference.E.Literal l){ return l.infName(); }
  private static TName guessImplName(inference.E.Literal l){
    if (!l.cs().isEmpty()){ return l.cs().getFirst().name(); }
    var rcc= (IT.RCC)l.t();
    return rcc.c().name();
    }
  static String bestNamePgk(Literal l){
    if (!useImplName(l)){ return disp(l.name().s()+genArity(l.name().arity())); }
    return "instance of "+disp(l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity()));
  }
  static String bestNamePgk(inference.E.Literal l){
    if (!useImplName(l)){ return disp(l.name().s()+genArity(l.name().arity())); }
    var n= guessImplName(l);
    return "instance of "+disp(n.s()+genArity(n.arity()));
  }
  static String up(String s){return s.substring(0, 1).toUpperCase() + s.substring(1); }
  static String expRepr(E toErr){return switch(toErr){
    case Call c->"method call "+Err.methodSig(c.name());
    case X x->"parameter " +Err.disp(x.name());
    case Literal l->l.thisName().equals("this")
      ? "type declaration " +typeDecName(l.name())
      : "object literal " +bestNamePgk(l);
    case Type t-> "object literal instance of " + t;
    };}
  static String expRepr(inference.E toErr){return switch(toErr){
    case inference.E.Call c->"method call "+Err.methodSig(c.name());
    case inference.E.ICall c->"method call "+Err.methodSig(c.name());
    case inference.E.X x->"parameter " +Err.disp(x.name());
    case inference.E.Literal l->l.thisName().equals("this")
      ? "type declaration " +typeDecName(l.name())
      : "object literal " +bestNamePgk(l);
    case inference.E.Type t-> "object literal instance of " + t;
    };}
  static String bestName(Literal l){
    if (!useImplName(l)){ return disp(l.name().simpleName()+genArity(l.name().arity())); }
    return "instanceOf "+disp(l.cs().getFirst().name().simpleName()+genArity(l.cs().getFirst().name().arity()));
  }
  static String bestName(inference.E.Literal l){
    if (!useImplName(l)){ return disp(l.name().simpleName()+genArity(l.name().arity())); }
    var n= guessImplName(l);
    return "instanceOf "+disp(n.simpleName()+genArity(n.arity()));
  }
  static String bestNameDirect(Literal l){
    if (!useImplName(l)){ return l.name().s()+genArity(l.name().arity()); }
    return l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity());
  }
  static String bestNameDirect(inference.E.Literal l){
    if (!useImplName(l)){ return l.name().s()+genArity(l.name().arity()); }
    return l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity());
  }
  static String genArity(int n){ return Join.of(IntStream.range(0, n).mapToObj(_->"_"),"[",",", "]","");}
  String text(){ return sb.toString().stripTrailing(); }
  public Err pTypeArgBounds(String what, String kindingTarget, String paramName,  int index, String badStr, String allowedStr){
  return line("The "+what+" is invalid.")
    .line("Type argument "+(index+1)+" ("+badStr+") does not satisfy the bounds for type parameter "+paramName+" in "+kindingTarget+".")
    .line("Here "+paramName+" can only use capabilities "+allowedStr+".");
  }
  public Err invalidMethImpl(Literal l, MName m){ return line("Invalid method implementation for "+methodSig(l,m)+"."); }
  FearlessException ex(pkgmerge.Package pkg, E e){
    return ex(pkg,"Compressed relevant code with inferred types: (compression indicated by `-`)",e);
  }
  FearlessException ex(pkgmerge.Package pkg, String footerHdr, core.E footerE){
    assert sb.length() != 0;
    assert footerHdr != null && footerE != null;
    return Code.TypeError.of(blank()
      .line(footerHdr)
      .compactPrinterLine(pkg, footerE)
      .text());
  }
  Err inferredContext(pkgmerge.Package pkg, TypeScope.Method scope,T reqT){
    List<T> interest= TypeScope.interestFromDeclVsReq(scope.m().sig().ret(), reqT);
    var best= TypeScope.bestInterestingScope(scope, interest);
    if (best.isTop()){ return this; }
    var ctx= best.contextE();
    return 
       line("Compressed surrounding code with inferred types: (compression indicated by `-`)")
      .compactPrinterLine(pkg, ctx);
  }
  Err compactPrinterLine(pkgmerge.Package pkg, E e){
    Map<String,String> map= pkg.map().entrySet().stream()
      .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
    var ee= new CompactPrinter(pkg.name(),map).limit(e,120);
    return line(ee);
  }
  Err line(String s){
    assert !s.isEmpty();
    assert sb.lastIndexOf("\n") == sb.length()-1;
    s= s.stripTrailing();
    sb.append(s).append("\n");
    return this;
  }
  Err blank(){
    int n= sb.length();
    assert n != 0;
    assert sb.charAt(n-1) == '\n';
    if (n >= 2 && sb.charAt(n-2) == '\n'){ return this; }
    sb.append('\n');
    return this;
  }
  Err bullet(String s){ return line(item("- ","  ", s)); }
  Err indented(String s){ return line(item("  ","  ", s)); }

  private String item(String first, String rest, String s){
    s= s.stripTrailing();
    assert !s.isEmpty();
    return first+s.replace("\n","\n"+rest);
  }

  Err pArgsDisagreeIntro(){
    return line("Each argument is compatible with at least one promotion, but no single promotion works for all arguments.");
  }
  Err pAcceptedByPromos(int argi, List<String> promos){
    assert !promos.isEmpty();
    return bullet(argLabel(argi)+" is compatible with promotions: "+Join.of(promos,"",", ","."));
  }

  Err pCallCantBeSatisfied(Call c){
    return line("This call to method "+methodSig(c.name())+" does not type-check.");
  }
  Err pMethodContext(String kind, Sig s, String where){
    line(kind+" for method "+methodSig(s.m())+".");
    return where.isEmpty() ? this : line("In "+disp(where)+".");
  }
  Err conflictsWithMethodIn(Sig sup){ return line("Conflicts with method in "+disp(sup.origin().s())+"."); }

  Err pPromotionFailuresHdr(){ return blank().line("Promotion failures:"); }
  Err pPromoFailure(String reason, String promo){
    reason= reason.stripTrailing();
    assert !reason.isEmpty();
    return bullet(reason.replaceFirst("\n", "    "+promo+"\n"));
  }
  public static boolean rcOnlyMismatch(T got, T req){
    return got.equals(req) 
        || (got instanceof T.RCC g 
        && req instanceof T.RCC r
        && g.c().equals(r.c()));
  }

//------
  Err pReceiverRequiredByPromotion(List<MType> promos){
    throw Bug.todo();/*var byRc= new LinkedHashMap<RC, List<String>>();
    for (var m:promos){
      var ps= byRc.computeIfAbsent(m.rc(), _->new ArrayList<>());
      String p= promoName(m.promotion());
      if (!ps.contains(p)){ ps.add(p); }
    }
    blank().line("Receiver required by each promotion:");
    byRc.keySet().stream()
      .sorted((a,b)->Integer.compare(a.ordinal(), b.ordinal()))
      .forEach(rc->bullet(disp(rc)+" ("+Join.of(byRc.get(rc),""," / ","")+")"));
    return this;*/
  }

  Err pHopelessArg(Call c, int argi, List<TRequirement> reqs, List<Reason> res){
    throw Bug.todo();/*pCallCantBeSatisfied(c);
    if (diag.isPresent()){ return blank().pArgDiag(diag.get()).pTypesRequiredByPromo(reqs); }
    var gotTs= res.stream().map(TResult::best).distinct().toList();
    pArgHasType(argi, gotTs);
    var byT= typesByPromo(reqs);
    var need= byT.keySet().stream()
      .sorted((a,b)->{
        int ra= rcRank(a), rb= rcRank(b);
        if (ra != rb){ return Integer.compare(ra, rb); }
        return disp(a).compareTo(disp(b));
      })
      .toList();
    var needS= need.stream().map(Err::disp).toList();
    String targets= needS.size() == 1 ? needS.getFirst() : "any of "+Join.of(needS,""," or ","");
    line("That is not a subtype of "+targets+".");
    return pTypesRequiredByPromo(byT, need);*/
  }

  /*private Err pArgHasType(int argi, List<T> gotTs){
    return line(argLabel(argi)+" has type "+dispTypes(gotTs)+".");
  }

  private Err pTypesRequiredByPromo(List<TRequirement> reqs){
    var byT= typesByPromo(reqs);
    var need= byT.keySet().stream()
      .sorted((a,b)->{
        int ra= rcRank(a), rb= rcRank(b);
        if (ra != rb){ return Integer.compare(ra, rb); }
        return disp(a).compareTo(disp(b));
      })
      .toList();
    return pTypesRequiredByPromo(byT, need);
  }
  private Err pTypesRequiredByPromo(Map<T, List<String>> byT, List<T> orderedTs){
    blank().line("Type required by each promotion:");
    for (var t:orderedTs){
      var ps= byT.get(t);
      assert ps != null && !ps.isEmpty();
      bullet(disp(t)+" ("+Join.of(ps,""," / ","")+")");
    }
    return this;
  }
  private Map<T, List<String>> typesByPromo(List<TRequirement> reqs){
    var m= new LinkedHashMap<T, List<String>>();
    for (var r:reqs){
      String p= promoName(r.reqName());
      assert !p.isEmpty();
      var ps= m.computeIfAbsent(r.t(), _->new ArrayList<>());
      if (!ps.contains(p)){ ps.add(p); }
    }
    return m;
  }*/
  public Err lineGotMsg(String label, T got, T expected){ return line(up(gotMsg(label,got, expected))); }
  private String argLabel(int argi){ return "Argument "+(argi+1); }
  private static boolean isInferErr(T t){
    return t instanceof T.RCC rcc && rcc.c().name().s().equals("base.InferErr");
  }
  public static String gotMsg(String label, T got, T expected){
    String g= disp(got);
    String e= disp(expected);
    if (isInferErr(expected)){ return label 
      + " cannot be checked agains an expected supertype.\n"
      + "Type inference could not infer an expected type; computed type is "+g+"."; }
    return label+" is used where "+e+" is required,\nbut it has type "+g+", which is not a subtype of "+e+".";
  }

  static String methodSig(MName m){ return methodSig("",m); }
  static String methodSig(TName pre, MName m){ return methodSig(tNameDirect(pre),m); }
  static String methodSig(Literal l, MName m){ return methodSig(bestNameDirect(l),m); }
  static String methodSig(inference.E.Literal l, MName m){ return methodSig(bestNameDirect(l),m); }
  static String methodSig(String pre, MName m){
    return disp(Join.of(
      IntStream.range(0,m.arity()).mapToObj(_->"_"),
      pre+m.s()+"(",",",")",
      pre+m.s()
    ));
  }

}