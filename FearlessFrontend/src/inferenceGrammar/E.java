package inferenceGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
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
    public E withT(IT t){ return new X(name,t,pos,t.isTV()); }
  }
  record Literal(String thisName, List<M> ms, IT t, Pos pos, long g) implements E{
    public Literal(String thisName, List<M> ms, Pos pos){ this(thisName,ms,IT.U.Instance,pos,0);}
    public Literal{
      assert unmodifiable(ms, "L.ms");
      assert nonNull(thisName,t);
    }
    public boolean isEV(){ return false; }
    public E withT(IT t){ return new Literal(thisName,ms,t,pos,g); }
    public String toString(){ return "{'"+thisName
      + ms.stream().map(Object::toString).collect(Collectors.joining(""))
      +"}:"+t; }
    public Literal withMs(List<M> ms){ return new Literal(thisName,ms,t,pos,0); }
  }
  record Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, IT t, Pos pos, boolean isEV, long g) implements E{
    public Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, Pos pos){ this(e,name,rc,targs,es,IT.U.Instance,pos,false,0);}
    public Call{
      assert nonNull(e,name,rc,targs,t);
      assert unmodifiable(es, "E.Call.es");
    }
    public Call withG(long g){ return new Call(e,name,rc,targs,es,t,pos,isEV,g); }
    public E withT(IT t){ return new Call(e,name,rc,targs,es,t,pos,t.isTV(),g); }
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
    public E withT(IT t){ return new ICall(e,name,es,t,pos,g); }
    //public ICall withG(long g){ return new ICall(e,name,es,t,pos,g); }
    public String toString(){ return ""+e+name+"("
        +es.stream().map(Object::toString).collect(Collectors.joining(","))+"):"+t;
      }
  }
  record Type(IT.RCC type, IT t, Pos pos, boolean isEV) implements E{
    public Type(IT.RCC type, Pos pos){ this(type,IT.U.Instance,pos,false); }
    public E withT(IT t){ return new Type(type,t,pos,t.isTV()); }
    public String toString(){ return ""+type+":"+t; }
  }
}