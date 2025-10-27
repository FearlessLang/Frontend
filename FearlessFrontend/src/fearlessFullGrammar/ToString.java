package fearlessFullGrammar;

import java.util.Iterator;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

import fearlessFullGrammar.E.*;
import fearlessFullGrammar.T.*;
import fearlessFullGrammar.XPat.Destruct;
import fearlessFullGrammar.XPat.Name;
import fearlessParser.RC;
import utils.Bug;

public class ToString implements EVisitor<StringBuilder>,TVisitor<StringBuilder>,XPatVisitor<StringBuilder>{
  public static String declaration(Declaration d){ 
    var v= new ToString();
    v.visitInnerDeclaration(d);
    return v.res.toString();
  }
  public static String t(T t){ 
    var v= new ToString();
    t.accept(v);
    return v.res.toString();
  }
  public static String c(T.C c){ 
    var v= new ToString();
    v.visitInnerC(c);
    return v.res.toString();
  }
  public static String e(E e){ 
    var v= new ToString();
    e.accept(v);
    return v.res.toString();
  }
  public static String sig(Sig sig){ 
    var v= new ToString();
    v.visitInnerSig(sig);
    return v.res.toString();
  }
  StringBuilder res= new StringBuilder();
  StringBuilder append(String s){ return res.append(s); }
  <EE>StringBuilder append(String start, List<EE> es, Consumer<EE> c,String sep, String end){
    append(start);
    boolean first= true;
    for (int i= 0; i < es.size(); i++){
      if (!first){ append(sep); }
      first= false;
      c.accept(es.get(i));
    }
    return append(end); 
    }
  @Override public StringBuilder visitXPatName(Name n){ return n.x().accept(this);  }
  @Override public StringBuilder visitXPatDestruct(Destruct d){ return append("{",
    d.extract(),
    ns->ns.forEach(n->append(n.s())),
    ",",
    "}").append(d.id().orElse(""));
  }  
  @Override public StringBuilder visitTX(T.X x){ return append(x.name()); }
  @Override public StringBuilder visitX(E.X n){ return append(n.name()); }
  @Override public StringBuilder visitRCX(RCX x){ return append(x.rc().name()).append(" ").append(x.x().name()); }
  @Override public StringBuilder visitReadImmX(ReadImmX x){ return append("read/imm ").append(x.x().name()); }
  @Override public StringBuilder visitRCC(RCC c){
    c.rc().ifPresent(rc->append(rc.name()).append(" "));
    visitInnerC(c.c());
    return res;
  }
  @Override public StringBuilder visitRound(Round r){
    append("(");
    r.e().accept(this);
    return append(")");
  }
  @Override public StringBuilder visitImplicit(Implicit n){ return append("::"); }
  @Override public StringBuilder visitTypedLiteral(TypedLiteral t){
    t.t().accept(this);
    t.l().ifPresent(l->{ append(" "); l.accept(this); });
    return res;
  }
  @Override public StringBuilder visitDeclarationLiteral(DeclarationLiteral c){
    c.rc().ifPresent(rc->append(rc.name()).append(" "));
    this.visitInnerDeclaration(c.dec());
    return res;
  }
  @Override public StringBuilder visitLiteral(Literal c){
    append("{");
    c.thisName().ifPresent(n->append("'").append(n.name()));
    c.methods().forEach(this::visitInnerM);
    return append("}");
  }
  @Override public StringBuilder visitCall(Call c){
    c.e().accept(this).append(" ").append(c.name().s());
    c.targs().ifPresent(cs ->{
      append("[");
      cs.rc().ifPresent(rc->append(rc.name()));
      if (cs.rc().isPresent() && !cs.ts().isEmpty()){ append(","); }
      append("", cs.ts(), t -> t.accept(this), ",", "]");
      });
    append(c.pars()?"(":(c.es().isEmpty()?"":" "));
    c.pat().ifPresent(pat->pat.accept(this).append("= "));
    append("",c.es(),e->e.accept(this),", ","");
    append(c.pars()?")":"");
    return res;
  }
  @Override public StringBuilder visitStringInter(StringInter i){
    i.e().ifPresent(e->e.accept(this).append(" "));
    String nl= i.simple()?"|`":"|\"";
    append("\n");
    var it= i.hashCounts().listIterator();
    append("#".repeat(it.next())+nl);
    for (int j= 0; j < i.es().size(); j++){
      appendMultiline(i.strings().get(j),it,h->"\n" + ("#".repeat(h)) + nl);
      int c= i.hashCounts().get(it.previousIndex());
      append("{".repeat(c));
      i.es().get(j).accept(this).append("}".repeat(c));
    }
    appendMultiline(i.strings().getLast(),it,h->"\n" + ("#".repeat(h)) + nl);
    return res;
  }
  @Override public Declaration visitInnerDeclaration(Declaration d){
    append(d.name().s());
    d.bs().ifPresent(bs->append("[",bs,this::visitInnerB,",","]"));
    append(": ");
    append("",d.cs(),this::visitInnerC,", ","");
    if(!d.cs().isEmpty()){ append(" "); }
    visitLiteral(d.l());
    return d;
    }
  @Override public M visitInnerM(M m){
    append(" ");
    m.sig().ifPresent(this::visitInnerSig);
    if (m.sig().isPresent() && m.body().isPresent()){ append(" -> "); }
    m.body().ifPresent(e->e.accept(this));
    append(";");
    return m; 
  }
  @Override public T.C visitInnerC(T.C c){
    append(c.name().s());
    c.ts().ifPresent(ts->append("[",ts,t->t.accept(this),",","]"));
    return c;
  }
  @Override public Sig visitInnerSig(Sig s){
    var p= s.hasParenthesis();
    s.rc().ifPresent(rc->append(rc.name()).append(" "));
    s.m().ifPresent(m->append(m.s()).append(p||s.parameters().isEmpty()?"":" "));
    s.bs().ifPresent(bs->append("[",bs,this::visitInnerB,",","]"));
    if (p){ append("("); }
    append("",s.parameters(),this::visitInnerParameter,", ","");
    if (p){ append(")"); }
    s.t().ifPresent(t->{append(": "); t.accept(this);});
    return s;
  }
  @Override public B visitInnerB(B b){
    b.x().accept(this);
    switch(b.bt()){
      case B.Star() -> append(":*");
      case B.StarStar() -> append(":**");
      case B.RCS(List<RC> rcs) -> {
        if(rcs.isEmpty()){ return b; }
        append(":",rcs,rc->append(rc.name()),",","");
        }
      };
    return b; 
    }
  @Override public Parameter visitInnerParameter(Parameter p){
    p.xp().ifPresent(xp->xp.accept(this));
    if(p.xp().isPresent() && p.t().isPresent()){ append(": "); }
    p.t().ifPresent(t->t.accept(this));
    return p;
  }  
  @Override public Literal visitInnerLiteral(Literal l){ throw Bug.unreachable(); }
  @Override public XPat visitInnerXPat(XPat x){ throw Bug.unreachable(); }
  @Override public CallSquare visitInnerCallSquare(CallSquare c){ throw Bug.unreachable(); }
  @Override public RCC visitInnerRCC(RCC t){ throw Bug.unreachable(); }
  private <EE> void appendMultiline(String s, Iterator<EE> it, Function<EE,String> f){
    int from= 0;
    int i;
    while ((i = s.indexOf('\n', from)) != -1){
      res.append(s, from, i);
      from = i + 1;
      if (it.hasNext()){ res.append(f.apply(it.next())); }
      else{ res.append('\n'); }
    }
    res.append(s, from, s.length());
  }
}