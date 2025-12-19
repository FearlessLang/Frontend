package message;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import inference.IT;
import metaParser.Message;
import typeSystem.TypeSystem.*;
import utils.Bug;

public record Err(Supplier<CompactPrinter> _cp, StringBuilder sb){
  CompactPrinter cp(){ return _cp.get(); }
  static String disp(Object o){ return Message.displayString(o.toString()); }
  static String genArity(int n){ return Join.of(IntStream.range(0, n).mapToObj(_->"_"),"[",",", "]","");}
  static String staticTypeDecName(TName name){ return disp(name.simpleName()+genArity(name.arity())); }
  String typeDecName(TName name){ return disp(name.simpleName()+genArity(name.arity())); }
  String typeDecNamePkg(TName name){ return disp(tNameDirect(name)); }
  String tNameDirect(TName n){ return n.s()+genArity(n.arity()); }
  static boolean useImplName(Literal l){ return l.infName(); }
  static boolean useImplName(inference.E.Literal l){ return l.infName(); }
  private TName guessImplName(inference.E.Literal l){
    if (!l.cs().isEmpty()){ return l.cs().getFirst().name(); }
    var rcc= (IT.RCC)l.t();
    return rcc.c().name();
    }
  String bestNamePkg(Literal l){
    if (!useImplName(l)){ return disp(l.rc().toStrSpace()+l.name().s()+genArity(l.name().arity())); }
    return "instance of "+disp(l.rc().toStrSpace()+l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity()));
  }
  String bestNamePkgDirect(boolean skipImm,Literal l){
    if (!useImplName(l)){ return disp(l.rc().toStrSpace(skipImm)+l.name().s()+genArity(l.name().arity())); }
    return disp(l.rc().toStrSpace(skipImm)+l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity()));
  }
  String bestNamePkg(inference.E.Literal l){
    if (!useImplName(l)){ return disp(l.rc().orElse(RC.imm).toStrSpace()+l.name().s()+genArity(l.name().arity())); }
    var n= guessImplName(l);
    return "instance of "+disp(l.rc().orElse(RC.imm).toStrSpace()+n.s()+genArity(n.arity()));
  }
  static String up(String s){return s.substring(0, 1).toUpperCase() + s.substring(1); }
  String expRepr(E toErr){return switch(toErr){
    case Call c->"method call "+methodSig(c.name());
    case X x->"parameter " +disp(x.name());
    case Literal l->l.thisName().equals("this")
      ? "type declaration " +typeDecName(l.name())
      : "object literal " +bestNamePkg(l);
    case Type t-> "object literal instance of " + t;
    };}
  String expReprDirect(boolean skipImm, E toErr){return switch(toErr){
    case Call c->methodSig(c.name());
    case X x->disp(x.name());
    case Literal l->l.thisName().equals("this")
      ? typeDecName(l.name())
      : bestNamePkgDirect(skipImm,l);
    case Type t-> t.toString();
    };}
  String bestNameHintExplicitRC(E e){ return switch(e){
    case Literal l-> l.rc() != RC.imm ? "" : bestNameDirect(l)+(l.infName()?"{...}":":{...}");
    case Type t ->  t.type().rc() != RC.imm ? "" : bestNameDirect(t);
    default ->{ throw Bug.unreachable(); }
  };}
  String expRepr(inference.E toErr){return switch(toErr){
    case inference.E.Call c->"method call "+methodSig(c.name());
    case inference.E.ICall c->"method call "+methodSig(c.name());
    case inference.E.X x->"parameter " +disp(x.name());
    case inference.E.Literal l->l.thisName().equals("this")
      ? "type declaration " +typeDecName(l.name())
      : "object literal " +bestNamePkg(l);
    case inference.E.Type t-> "object literal instance of " + t;
    };}
  String bestNameDirect(Literal l){
    if (!useImplName(l)){ return l.name().s()+genArity(l.name().arity()); }
    return l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity());
  }
  String bestNameDirect(E.Type l){
    return l.type().rc().toStrSpace()+tNameDirect(l.type().c().name())+genArity(l.type().c().name().arity());
  }
  String bestNameDirect(inference.E.Literal l){
    if (!useImplName(l)){ return l.name().s()+genArity(l.name().arity()); }
    return l.cs().getFirst().name().s()+genArity(l.cs().getFirst().name().arity());
  }
  static String methodSig(MName m){ return methodSig("",m); }
  String methodSig(TName pre, MName m){ return methodSig(tNameDirect(pre),m); }
  String methodSig(Literal l, MName m){ return methodSig(bestNameDirect(l),m); }
  String methodSig(inference.E.Literal l, MName m){ return methodSig(bestNameDirect(l),m); }
  static String methodSig(String pre, MName m){
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
  public Err invalidMethImpl(Literal l, MName m){ return line("Invalid method implementation for "+methodSig(l,m)+"."); }

  Err compactPrinterLine(E e){ return line(cp().limit(e,120)); }
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
    return line("This call to method "+methodSig(d,c.name())+" can not typecheck.");
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
  public static String gotMsg(String label, T got, T expected){
    if (!isInferErr(expected)){ return label+" has type "+disp(got)+" instead of a subtype of "+disp(expected)+"."; }
    return gotMsgInferErr(label,got); 
    }
  public static String gotMsgInferErr(String label, T got){
    return label 
      + " cannot be checked agains an expected supertype.\n"
      + "Type inference could not infer an expected type; computed type is "+disp(got)+"."; 
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
}