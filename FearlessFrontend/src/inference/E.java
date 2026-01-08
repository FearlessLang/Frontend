package inference;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;

import core.B;
import core.MName;
import core.RC;
import core.Src;
import core.TName;
import core.TSpan;
import utils.Join;
import utils.Pos;

public sealed interface E {
  default Pos pos(){ return src().inner.pos(); }
  default TSpan span(){ return src().inner.span(); }
  Src src();
  IT t();
  E withT(IT t);
  default void sign(Gamma gamma){ gamma.sign(g()); }
  default boolean done(Gamma gamma){ return gamma.represents(g()); }
  Gamma.GammaSignature g();
  record X(String name, IT t, Src src, Gamma.GammaSignature g) implements E{
    public X(String name, Src src){ this(name,IT.U.Instance,src,new Gamma.GammaSignature()); }
    public X{ assert nonNull(t) && validate(name, "parameter name",LowercaseId); }
    public String toString(){ return name+":"+t; }
    public E withT(IT t){
      assert Monotonicity.eT(g, this, this.t, t);
      if (t.equals(this.t)){ return this; }
      return new X(name,t,src,g.clear());
    }
  }
  record Type(IT.RCC type, IT t, Src src, Gamma.GammaSignature g) implements E{
    public Type{ assert nonNull(type,t,src,g); }
    public Type(IT.RCC type, Src src){ this(type,IT.U.Instance,src,new Gamma.GammaSignature()); }
    public E withT(IT t){
      assert Monotonicity.eT(g, this, this.t, t);
      if (t.equals(this.t)){ return this; }
      return new Type(type,t,src,g.clear());
    }
    public String toString(){ return ""+type+":"+t; }
  }
  // **rc is present implies no inference needed**
  record Literal(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, IT t, Src src,boolean infName, boolean infHead, Gamma.GammaSignature g) implements E{
    public Literal(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, Src src,boolean infName){
      this(rc,name,bs,cs,thisName,ms,IT.U.Instance,src,infName,false,new Gamma.GammaSignature());
    }    
    public Literal{
      assert unmodifiableDistinct(bs,"L.bs");
      assert unmodifiable(cs,"L.cs");
      assert unmodifiableDistinct(ms, "L.ms");
      assert nonNull(name,thisName,t);
      }
    public E.Literal withT(IT t){
      assert Monotonicity.eT(g, this, this.t, t);
      if (t.equals(this.t)){ return this; }
      return new Literal(rc,name,bs,cs,thisName,ms,t,src,infName,infHead,g.clear());
    }
    public String toString(){
      String res= rc.map(RC::toStrSpace).orElse("");
      res += name.s();
      res += Join.of(bs,"[",",","]","");
      res += rc.isEmpty()
        ?":$?"
        :Join.of(cs,":",", ","",":");
      if (ms.isEmpty()){ return res+":"+t; }
      res += "{'"+thisName;
      res += Join.of(ms,"","","","");
      res +="}:"+t;
      return res;
    }
    public Literal withMs(List<M> ms){
      assert t instanceof IT.RCC:t;
      assert Monotonicity.onLiteralWithMs(this, ms);
      if (infHead && ms == this.ms){ return this; } 
      return new Literal(rc,name,bs,cs,thisName,ms,t,src,infName,true,g.clear());
    }
    public Literal withMsT(List<M> ms, IT t){
      assert t instanceof IT.RCC:t;
      assert Monotonicity.onLiteralWithMs(this, ms);
      assert Monotonicity.eT(g, this, this.t, t);
      if (infHead && ms == this.ms && t.equals(this.t)){ return this; }
      assert !t.equals(this.t) || ms == this.ms || !ms.equals(this.ms) : "Allocated equal MS:\n"+ms;
      return new Literal(rc,name,bs,cs,thisName,ms,t,src,infName,true,g.clear());
    }
    public Literal withCsMs(List<IT.C> cs, List<M> ms, boolean setInfHead){
      assert !setInfHead || !infHead;
      assert !setInfHead || t instanceof IT.RCC:t;
      var noChange= infHead == setInfHead && cs.equals(this.cs) && ms == this.ms;
      if (noChange){ return this; }
      assert Monotonicity.onLiteralWithMs(this, ms);
      assert ms == this.ms || !ms.equals(this.ms) : "Allocated equal MS:\n"+ms;
      return new Literal(rc,name,bs,cs,thisName,ms,t,src,infName,setInfHead,g.clear());
    }
  }
  record Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, IT t, Src src, Gamma.GammaSignature g) implements E{
    public Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, Src src){
      this(e,name,rc,targs,es,IT.U.Instance,src,new Gamma.GammaSignature());
    }
    public Call{
      assert nonNull(e,name,rc,targs,t);
      assert unmodifiable(es, "E.Call.es");
      assert unmodifiable(targs, "E.Call.targs");
    }
    public Call withMore(E e,RC rc,List<IT> targs,List<E> es,IT t){
      assert e == this.e || !e.equals(this.e) : "Allocated equal receiver E";
      assert es == this.es || !es.equals(this.es) : "Allocated equal es list";
      assert Monotonicity.onCallWithMore(this, Optional.of(rc), targs, t);
      if (e == this.e && Optional.of(rc).equals(this.rc) && targs.equals(this.targs) && es == this.es && t.equals(this.t)){ return this; } 
      return new E.Call(e, name, Optional.of(rc),targs,es,t,src,g.clear());
    }
    public Call withEEs(E e,List<E> es){
      assert e == this.e || !e.equals(this.e) : "Allocated equal receiver E";
      assert es == this.es || !es.equals(this.es) : "Allocated equal es list";
      if (e == this.e && es == this.es){ return this; }
      return new E.Call(e, name, rc,targs,es,t,src,g.clear());
    }
    public Call withE(E e){
      assert e == this.e || !e.equals(this.e) : "Allocated equal receiver E";
      if (e == this.e){ return this; }
      return new E.Call(e, name, rc,targs,es,t,src,g.clear());
    }
    public Call withT(IT t){
      assert Monotonicity.eT(g, this, this.t, t);
      if (t.equals(this.t)){ return this; }
      return new Call(e,name,rc,targs,es,t,src,g.clear());
    }
    public String toString(){ 
      var open= rc.isEmpty()? "[" : "["+rc.get();
      return ""+e+name+open
        +Join.of(targs,rc.isEmpty()?"":",",",","](","](")
        +Join.of(es,"",",","):","):")+t;
    }
  }
  record ICall(E e, MName name, List<E> es, IT t, Src src, Gamma.GammaSignature g) implements E{
    public ICall(E e, MName name, List<E> es, Src src){ this(e,name,es,IT.U.Instance,src,new Gamma.GammaSignature());}
    public E withT(IT t){
      assert Monotonicity.eT(g, this, this.t, t);
      if (t.equals(this.t)){ return this; }
      return new ICall(e,name,es,t,src,g.clear()); 
    }
    public String toString(){ return ""+e+name+Join.of(es,"(",",","):","():")+t; }
    public E withEEs(E e, List<E> es) {
      assert e == this.e || !e.equals(this.e) : "Allocated equal receiver E";
      assert es == this.es || !es.equals(this.es) : "Allocated equal es list";
      if (e == this.e && es == this.es){ return this; } 
      return new ICall(e,name,es,t,src,g.clear());
    }
    public E withE(E e) {
      assert e == this.e || !e.equals(this.e) : "Allocated equal receiver E";
      if (e == this.e){ return this; } 
      return new ICall(e,name,es,t,src,g.clear());
    }
  }
}