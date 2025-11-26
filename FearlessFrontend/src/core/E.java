package core;

import files.Pos;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.*;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;

public sealed interface E {
  Pos pos();
  record X(String name, Pos pos) implements E{
    public X{ assert validate(name, "parameter name",LowercaseId); }
    public String toString(){ return name;}}
  record Type(T.RCC type, Pos pos) implements E{
    public Type{ assert nonNull(type,pos); }
    public String toString(){ return type.toString();}}
  record Literal(RC rc, TName name, List<B> bs, List<T.C> cs, String thisName, List<M> ms, Pos pos) implements E{
    public Literal{
      assert unmodifiableDistinct(bs,"L.bs");
      assert unmodifiableDistinct(cs,"L.cs");
      assert unmodifiableDistinct(ms, "L.ms");
      assert nonNull(rc,name,thisName,pos);
    }
    public Literal withMs(List<M> ms){ return new Literal(rc,name,bs,cs,thisName,ms,pos); }
    public String toString(){
      String _bs= "";
      if (!bs.isEmpty()){ _bs = "["+bs.stream().map(Object::toString).collect(Collectors.joining(","))+"]"; }
      String _cs= cs.stream().map(Object::toString).collect(Collectors.joining(", "));
      String _ms= ms.stream().map(Object::toString).collect(Collectors.joining("; "));
      return rc+" "+name.s()+_bs+":"+_cs+"{'"+thisName+" "+_ms+"}";
    }
  }
  record Call(E e, MName name, RC rc, List<T> targs, List<E> es, Pos pos) implements E{
    public Call{
      assert nonNull(e,name,rc,targs,pos);
      assert unmodifiable(es, "E.Call.es");
      assert unmodifiable(targs, "E.Call.targs");
    }
    public String toString(){
      String _targs= "["+rc;
      if (!targs.isEmpty()){ _targs += ","+targs.stream().map(Object::toString).collect(Collectors.joining(",")); }
      String _es= "";
      if (!es.isEmpty()){ _es = "("+es.stream().map(Object::toString).collect(Collectors.joining(", "))+")"; }
      return ""+e+name+_targs+"]"+_es;
    }
  }
}