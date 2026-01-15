package message;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.function.Function;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import inject.TypeRename;
import metaParser.Message;
import typeSystem.TypeSystem.*;
import utils.Join;

public record Err(Function<T.C,T.C> publicHead, Function<TName,TName> preferredForFresh, Function<Boolean,CompactPrinter> _cp, StringBuilder sb){
  CompactPrinter cp(){ return _cp.apply(false); }
  CompactPrinter cp(boolean trunk){ return _cp.apply(trunk); }
  public static String disp(Object o){ return Message.displayString(o.toString()); }
  static String genArity(int n){ return Join.of(IntStream.range(0, n).mapToObj(_->"_"),"[",",", "]","");}
  static String staticTypeDecName(TName name){ return disp(name.simpleName()+genArity(name.arity())); }//for the parser only
  
  String tNameA(TName n){ return cp().msgTName(n)+genArity(n.arity()); }     // "A[_]"
  String tNameADisp(TName n){ return disp(tNameA(n)); }                      // displayString("A[_]")
  private boolean showInstanceOf(Literal l){ return l.infName() && !l.cs().isEmpty(); }
  private String bestLitName(boolean skipRc,boolean skipImm,Literal l){
    RC rc= skipRc?RC.imm:l.rc();
    if (showInstanceOf(l)){ return typeReprRaw(skipImm||skipRc,new T.RCC(rc,l.cs().getFirst(),l.span())); }
    if (l.infName() && l.cs().isEmpty()){ return anonRepr; }
    return rc.toStrSpace(skipImm)+tNameA(l.name());
  }
  private String bestLitName(inference.E.Literal l){
    return l.infName() ? tNameA(guessImplName(l)) : tNameA(l.name());
  }
  private TName guessImplName(inference.E.Literal l){
    if (!l.cs().isEmpty()){ return l.cs().getFirst().name(); }
    var rcc= (T.RCC)TypeRename.itToT(l.t());
    return rcc.c().name();
  }
  private String bestNamePkg0(boolean instanceOf, String n){
    return instanceOf ? "instance of "+disp(n) : disp(n);
  }
  private boolean anonLit(Literal l){ return l.infName() && l.cs().isEmpty(); }
  private final static String anonRepr="{...}"; 
  private String typeOrAnon(Literal l,String typePrefix,String anonPrefix){
    if (anonLit(l)){ return anonPrefix + disp(anonRepr); }
    return typePrefix+disp(bestLitName(false,true,l));
  }
  String onTypeOrAnon(Literal l){ return typeOrAnon(l,"object literal instance of ",""); }
  String theTypeOrObjectLiteral(Literal l){ return typeOrAnon(l,"type ","object literal "); }
  public String bestNameNoRc(Literal l){ return bestNamePkg0(showInstanceOf(l), bestLitName(true,true,l)); }
  T.C preferredForFresh(T.C t){ return new T.C(preferredForFresh.apply(t.name()).withArity(t.ts().size()),t.ts()); }//Correct to not propagate here
  T preferredForFresh(T t){ return switch(t){
    case T.X x -> x;
    case T.RCX x -> x;
    case T.ReadImmX x -> x;
    case T.RCC(RC rc, var c, var span) -> new T.RCC(rc, preferredForFresh(c),span);
  };}
  String typeRepr(inference.IT t){ return typeRepr(true,TypeRename.itToT(t)); }
  String typeRepr(boolean skipImm, T t){ return disp(typeReprRaw(skipImm,t)); }
  private String typeReprRaw(boolean skipImm, T t){
    var str= cp().msgT(showPublicHead(t));
    if (skipImm || !explicitImmRc(t)){ return str; }
    return "imm "+str;
  }
  T showPublicHead(T t){ return switch(t){
    case T.X x -> x;
    case T.RCX x -> x;
    case T.ReadImmX x -> x;
    case T.RCC(RC rc, T.C c, var span) -> new T.RCC(rc, publicHead.apply(c), span);
  };}
  String typeRepr(T.C t){ return disp(cp().msgT(new T.RCC(RC.imm, preferredForFresh(t),t.span()))); }
  static String up(String s){return s.substring(0, 1).toUpperCase() + s.substring(1); }
  String expRepr(E toErr){return switch(toErr){
    case Call c->"method call "+methodSig(c.name());
    case X x->"parameter " +displayX(x);
    case Literal l->l.thisName().equals("this")
      ? "type declaration " +tNameADisp(l.name())
      : "object literal " +bestNamePkg0(showInstanceOf(l), bestLitName(false,true,l));
    case Type t-> "object literal instance of " + typeRepr(true,t.type());
    };}
  String displayX(X x){
    core.Src.SrcObj src= x.src().inner;
    var impl= src instanceof fearlessFullGrammar.E.Implicit;
    if (impl){ return disp("::"); }
    return disp(x.name());
    }
  String expReprDirect(boolean skipImm, E toErr){return switch(toErr){
    case Call c->methodSig(c.name());
    case X x->disp(x.name());
    case Literal l->l.thisName().equals("this")
      ? tNameADisp(l.name())
      : bestNamePkg0(false, bestLitName(false,skipImm,l));
    case Type(var t,_) -> typeRepr(skipImm,t);  
    };}
  String expRepr(inference.E toErr){return switch(toErr){
    case inference.E.Call c->"method call "+methodSig(c.name());
    case inference.E.ICall c->"method call "+methodSig(c.name());
    case inference.E.X x->"parameter " +disp(x.name());
    case inference.E.Literal l->l.thisName().equals("this")
      ? "type declaration " +tNameADisp(l.name())
      : "object literal " +bestNamePkg0(l.infName(), bestLitName(l));
    case inference.E.Type t-> "object literal instance of " + t;
    };}
  String methodSig(MName m){ return methodSig("",m); }
  String methodSig(String pre, TName t, MName m){ return methodSig(pre+tNameA(t),m); }
  String methodSig(String pre, Literal l, MName m){ return methodSig(pre+bestLitName(true,true,l),m); }
  String methodSig(String pre, inference.E.Literal l, MName m){ return methodSig(pre+bestLitName(l),m); }
  String methodSig(String pre, MName m){
    return disp(Join.of(
      IntStream.range(0,m.arity()).mapToObj(_->"_"),
      pre+m.s()+"(",",",")",
      pre+m.s()
    ));
  }
  public static boolean rcOnlyMismatch(T got, T req){
    return got.equals(req) 
      || (got instanceof T.RCC g 
      && req instanceof T.RCC r
      && g.c().equals(r.c()));
  }
  public static boolean explicitImmRc(T t){ return switch(t){
    case T.RCX(RC rc, _) -> rc == RC.imm;
    case T.RCC(RC rc, _, _) -> rc == RC.imm;
    default -> false;
  };}  
  static boolean isInferErr(T t){
    return t instanceof T.RCC rcc && rcc.c().name().s().equals("base.InferErr");
  }  
  String text(){ return sb.toString().stripTrailing(); }
  public Err pTypeArgBounds(String what, String kindingTarget, String paramName,  int index, String badStr, String allowedStr){
    return line("The "+what+" is invalid.")
      .line("Type argument "+(index+1)+" ("+badStr+") does not satisfy the bounds")
      .line("for type parameter "+paramName+" in "+kindingTarget+".")
      .line("Here "+paramName+" can only use capabilities "+allowedStr+".");
  }
  public Err invalidMethImpl(String pre,Literal l, MName m){ 
    return line("Invalid method signature overriding for "+methodSig(pre,l,m)+".");
  }

  Err compactPrinterLine(E e){ return line(cp(true).limit(e,120)); }
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

  private String item(String first, String rest, String s){
    s= s.stripTrailing();
    assert !s.isEmpty();
    return first+s.replace("\n","\n"+rest);
  }
  Err pCallCantBeSatisfied(Literal d, Call c){
    return line("This call to method "+methodSig(c.rc().toStrSpace(),d,c.name())+" can not typecheck.");
  }
  Err notInSubtypeList(List<String> options){
    if (options.size() == 1){ return this; };
    return line(Join.of(options,"That is not a subtype of any of "," or ","."));
  }
  Err pCallCantBeSatisfied(Call c){
    return line("This call to method "+methodSig(c.name())+" can not typecheck.");
  }
  Err pPromotionFailuresHdr(){ return blank().line("Promotion failures:"); }
  Err pPromoFailure(String reason){
    reason= reason.stripTrailing();
    assert !reason.isEmpty();
    return bullet(reason);
  }
  Err pReceiverRequiredByPromotion(List<MType> promos){
    var byRc= new LinkedHashMap<RC, List<String>>();
    for (var m:promos){
      var ps= byRc.computeIfAbsent(m.rc(), _->new ArrayList<>());
      String p= m.promotion();
      if (!ps.contains(p)){ ps.add(p); }
    }
    if (byRc.size() > 1){
      blank().line("Receiver required by each promotion:");
      byRc.keySet().stream()
        .sorted((a,b)->Integer.compare(a.ordinal(), b.ordinal()))
        .forEach(rc->bullet(disp(rc)+" ("+Join.of(byRc.get(rc),""," / ","")+")"));
    }
    return this;
  }
  public String gotMsg(boolean skipImm,String label, T got, T expected){
    if (isInferErr(expected)){ return gotMsgInferErr(label,got); }
    return label+" has type "+ typeRepr(skipImm,got)+" instead of a subtype of "+typeRepr(skipImm,expected)+".";  
  }
  public String gotMsgInferErr(String label, T got){
    return label 
      + " cannot be checked agains an expected supertype.\n"
      + "Type inference could not infer an expected type; computed type is "+typeRepr(true,got)+"."; 
    }
    
  FearlessException ex(E e){
    return ex("Compressed relevant code with inferred types: (compression indicated by `-`)",e);
  }
  FearlessException exInferMsg(E e, String req){
    return ex("See inferred typing context below for how type "+req+" was introduced: (compression indicated by `-`)", e);
  }
  FearlessException ex(String footerHdr, core.E footerE){
    assert sb.length() != 0;
    assert footerHdr != null && footerE != null;
    return Code.TypeError.of(blank()
      .line(footerHdr)
      .compactPrinterLine(footerE)
      .text());
  }
  FearlessException wf(){
    assert sb.length() != 0;
    return Code.WellFormedness.of(text());
  }
}