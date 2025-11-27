package core;

import files.Pos;
import message.Join;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.*;

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
      String _bs= Join.of(bs,"[",",","]","");
      String _cs= Join.of(cs,"",", ","","");
      String _ms= Join.of(ms,"","; ","","");
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
      String _targs= Join.of(targs,"["+rc+",",",","","["+rc);
      String _es= Join.of(es,"(",", ",")","");
      return ""+e+name+_targs+"]"+_es;
    }
  }
}