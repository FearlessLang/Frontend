package inferenceGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;

public sealed interface E {
  Pos pos();
  IT t();
  boolean isEV();
  E withT(IT t);
  record X(String name, IT t, Pos pos, boolean isEV) implements E{
    public X(String name, Pos pos){ this(name,IT.U.Instance,pos,false); }
    public X{ assert nonNull(t) && validate(name, "parameter name",LowercaseId); }
    public String toString(){ return name+":"+t; }
    public E withT(IT t){
      if (t.equals(this.t)){ return this; }
      return new X(name,t,pos,t.isTV());
    }
  }
  record Type(IT.RCC type, IT t, Pos pos, boolean isEV) implements E{
    public Type(IT.RCC type, Pos pos){ this(type,IT.U.Instance,pos,false); }
    public E withT(IT t){ return new Type(type,t,pos,t.isTV()); }
    public String toString(){ return ""+type+":"+t; }
  }
  // **rc is present implies no inference needed**
  record Literal(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, IT t, Pos pos, boolean infA, long g) implements E{
    public Literal(Optional<RC> rc, TName name, List<B> bs, List<IT.C> cs, String thisName, List<M> ms, Pos pos){ this(rc,name,bs,cs,thisName,ms,IT.U.Instance,pos,false,0);}
    public Literal{
      assert unmodifiable(bs,"L.bs");
      assert unmodifiable(cs,"L.cs");
      assert unmodifiable(ms, "L.ms");
      assert nonNull(name,thisName,t);
    }
    public boolean isEV(){ return false; }
    public E withT(IT t){
      if (t.equals(this.t)){ return this; }
      return new Literal(rc,name,bs,cs,thisName,ms,t,pos,infA,0);
    }
    public String toString(){
      String res= "";
      assert cs.isEmpty() || rc.isPresent();
      if (rc.isPresent() && rc.get() != RC.imm){ res= rc.get()+" "; }
      res += name.s();
      if (!bs.isEmpty()){ res += "["+bs.stream().map(Object::toString).collect(Collectors.joining(","))+"]"; }
      if (rc.isEmpty()){ res += ":@"; }
      else { res += ":" +cs.stream().map(Object::toString).collect(Collectors.joining(", ")); }
      if (ms.isEmpty()){ return res+":"+t; }
      res += "{'"+thisName;
      res += ms.stream().map(Object::toString).collect(Collectors.joining(""));
      res +="}:"+t;
      return res;
    }
    public Literal withMs(List<M> ms, boolean infA){ return new Literal(rc,name,bs,cs,thisName,ms,t,pos,infA,0); }
    public Literal withMsT(List<M> ms, IT t, boolean infA){ return new Literal(rc,name,bs,cs,thisName,ms,t,pos,infA,0); }
    public Literal withCsMs(List<IT.C> cs, List<M> ms, boolean infA){ return new Literal(rc,name,bs,cs,thisName,ms,t,pos,infA,0); }
    public Literal withFlag(long g){ return new Literal(rc,name,bs,cs,thisName,ms,t,pos,infA,g); }
  }
  record Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, IT t, Pos pos, boolean isEV, long g) implements E{
    public Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, Pos pos){ this(e,name,rc,targs,es,IT.U.Instance,pos,false,0);}
    public Call{
      assert nonNull(e,name,rc,targs,t);
      assert unmodifiable(es, "E.Call.es");
    }
    public Call withFlag(long g){ return new Call(e,name,rc,targs,es,t,pos,isEV,g); }
    public E withT(IT t){
      if (t.equals(this.t)){ return this; }
      return new Call(e,name,rc,targs,es,t,pos,t.isTV(),0);
    }
    public String toString(){ 
      var open= rc.isEmpty()? "[" : targs.isEmpty() ? "["+rc.get() : "["+rc.get()+",";
      return ""+e+name+open
      +targs.stream().map(Object::toString).collect(Collectors.joining(","))+"]("
      +es.stream().map(Object::toString).collect(Collectors.joining(","))+"):"+t;
    }
  }
  record ICall(E e, MName name, List<E> es, IT t, Pos pos, long g) implements E{
    public ICall(E e, MName name, List<E> es, IT t, Pos pos){ this(e,name,es,IT.U.Instance,pos,0);}
    public boolean isEV(){ return false; }
    public E withT(IT t){
      if (t.equals(this.t)){ return this; }
      return new ICall(e,name,es,t,pos,0); 
    }
    //public ICall withG(long g){ return new ICall(e,name,es,t,pos,g); }
    public String toString(){ return ""+e+name+"("
        +es.stream().map(Object::toString).collect(Collectors.joining(","))+"):"+t;
      }
  }
}