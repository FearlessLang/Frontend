package fearlessFullGrammar;

import java.util.List;
import java.util.function.Consumer;
import core.RC;
import fearlessFullGrammar.E.*;
import fearlessFullGrammar.T.*;
import fearlessFullGrammar.XPat.Destruct;
import fearlessFullGrammar.XPat.Name;

public class ToString{
  public static String declaration(Declaration d){ 
    var v= new ToString();
    v.visitInnerDeclaration(d);
    return v.res.toString();
  }
  public static String t(T t){ 
    var v= new ToString();
    v.visitT(t);
    return v.res.toString();
  }
  public static String c(T.C c){ 
    var v= new ToString();
    v.visitInnerC(c);
    return v.res.toString();
  }
  public static String e(E e){ 
    var v= new ToString();
    v.visitE(e);
    return v.res.toString();
  }
  public static String sig(Sig sig){ 
    var v= new ToString();
    v.visitInnerSig(sig);
    return v.res.toString();
  }
  StringBuilder res= new StringBuilder();
  StringBuilder append(String s){ return res.append(s); }
  <EE>StringBuilder append(String start, List<EE> es, Consumer<EE> c, String sep, String end){
    append(start);
    for (int i= 0; i < es.size(); i += 1){
      if (i > 0){ append(sep); }
      c.accept(es.get(i));
    }
    return append(end);
  }    
  StringBuilder visitT(T t){ return switch (t){ case T.X x -> visitTX(x); case RCX x -> visitRCX(x); case ReadImmX x -> visitReadImmX(x); case RCC c -> visitRCC(c); }; }
  StringBuilder visitE(E e){
    return switch (e){
      case E.X x -> visitX(x);
      case Round r -> visitRound(r);
      case Implicit n -> visitImplicit(n);
      case TypedLiteral t -> visitTypedLiteral(t);
      case DeclarationLiteral c -> visitDeclarationLiteral(c);
      case Literal l -> visitLiteral(l);
      case Call c -> visitCall(c);
    };
  }
  StringBuilder visitXPat(XPat p){ return switch (p){ case Name n -> visitXPatName(n); case Destruct d -> visitXPatDestruct(d); }; }
  StringBuilder visitXPatName(Name n){ return visitX(n.x());  }
  StringBuilder visitXPatDestruct(Destruct d){ return append("{",
    d.extract(),
    ns->ns.forEach(n->append(n.s())),
    ",",
    "}").append(d.id().orElse(""));
  }  
  StringBuilder visitTX(T.X x){ return append(x.name()); }
  StringBuilder visitX(E.X n){ return append(n.name()); }
  StringBuilder visitRCX(RCX x){ return append(x.rc().name()).append(" ").append(x.x().name()); }
  StringBuilder visitReadImmX(ReadImmX x){ return append("read/imm ").append(x.x().name()); }
  StringBuilder visitRCC(RCC c){
    c.rc().ifPresent(rc->append(rc.name()).append(" "));
    visitInnerC(c.c());
    return res;
  }
  StringBuilder visitRound(Round r){
    append("(");
    visitE(r.e());
    return append(")");
  }
  StringBuilder visitImplicit(Implicit n){ return append("::"); }
  StringBuilder visitTypedLiteral(TypedLiteral t){
    visitRCC(t.t());
    t.l().ifPresent(l->{ append(" "); visitLiteral(l); });
    return res;
  }
  StringBuilder visitDeclarationLiteral(DeclarationLiteral c){
    c.rc().ifPresent(rc->append(rc.name()).append(" "));
    this.visitInnerDeclaration(c.dec());
    return res;
  }
  StringBuilder visitLiteral(Literal c){
    append("{");
    c.thisName().ifPresent(n->append("'").append(n.name()));
    c.methods().forEach(this::visitInnerM);
    return append("}");
  }
  StringBuilder visitCall(Call c){
    visitE(c.e()).append(" ").append(c.name().s());
    c.targs().ifPresent(cs ->{
      append("[");
      cs.rc().ifPresent(rc->append(rc.name()));
      if (cs.rc().isPresent() && !cs.ts().isEmpty()){ append(","); }
      append("", cs.ts(), this::visitT, ",", "]");
      });
    append(c.pars()?"(":(c.es().isEmpty()?"":" "));
    c.pat().ifPresent(pat->visitXPat(pat).append("= "));
    append("",c.es(),this::visitE,", ","");
    append(c.pars()?")":"");
    return res;
  }
  private Declaration visitInnerDeclaration(Declaration d){
    append(d.name().s());
    d.bs().ifPresent(bs->append("[",bs,this::visitInnerB,",","]"));
    append(": ");
    append("",d.cs(),this::visitInnerC,", ","");
    if (!d.cs().isEmpty()){ append(" "); }
    visitLiteral(d.l());
    return d;
    }
  private M visitInnerM(M m){
    append(" ");
    m.sig().ifPresent(this::visitInnerSig);
    if (m.sig().isPresent() && m.body().isPresent()){ append(" -> "); }
    m.body().ifPresent(this::visitE);
    append(";");
    return m; 
  }
  private T.C visitInnerC(T.C c){
    append(c.name().s());
    c.ts().ifPresent(ts->append("[",ts,this::visitT,",","]"));
    return c;
  }
  private Sig visitInnerSig(Sig s){
    var p= s.hasParenthesis();
    s.rc().ifPresent(rc->append(rc.name()).append(" "));
    s.m().ifPresent(m->append(m.s()).append(p || s.parameters().isEmpty()?"":" "));
    s.bs().ifPresent(bs->append("[",bs,this::visitInnerB,",","]"));
    if (p){ append("("); }
    append("",s.parameters(),this::visitInnerParameter,", ","");
    if (p){ append(")"); }
    s.t().ifPresent(t->{append(": "); visitT(t);});
    return s;
  }
  private B visitInnerB(B b){
    visitTX(b.x());
    switch (b.bt()){
      case B.Star() -> append(":*");
      case B.StarStar() -> append(":**");
      case B.RCS(List<RC> rcs) -> {
        if (rcs.isEmpty()){ return b; }
        append(":",rcs,rc->append(rc.name()),",","");
        }
      };
    return b; 
    }
  private Parameter visitInnerParameter(Parameter p){
    p.xp().ifPresent(this::visitXPat);
    if (p.xp().isPresent() && p.t().isPresent()){ append(": "); }
    p.t().ifPresent(this::visitT);
    return p;
  }
}