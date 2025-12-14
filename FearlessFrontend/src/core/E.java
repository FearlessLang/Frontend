package core;

import files.Pos;
import message.Join;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.*;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import fearlessParser.RC;

public sealed interface E {
  default Pos pos(){ return src().inner.pos(); }
  default TSpan span(){ return src().inner.span(); }
  Src src();
  record X(String name, Src src) implements E{
    public X{ assert name.equals("-") || validate(name, "parameter name",LowercaseId); }
    public String toString(){ return name;}}
  record Type(T.RCC type, Src src) implements E{
    public Type{ assert nonNull(type,src); }
    public String toString(){ return type.toString();}}
  record Literal(RC rc, TName name, List<B> bs, List<T.C> cs, String thisName, List<M> ms, Src src) implements E{
    public Literal{
      assert unmodifiableDistinct(bs,"L.bs");
      assert unmodifiableDistinct(cs,"L.cs");
      assert unmodifiableDistinct(ms, "L.ms");
      assert nonNull(rc,name,thisName,src);
    }
    public Literal withMs(List<M> ms){ return new Literal(rc,name,bs,cs,thisName,ms,src); }
    public String toString(){
      String _bs= Join.of(bs,"[",",","]","");
      String _cs= Join.of(cs,"",", ","","");
      String _ms= Join.of(ms,"","; ","","");
      return rc+" "+name.s()+_bs+":"+_cs+"{'"+thisName+" "+_ms+"}";
    }
  }
  record Call(E e, MName name, RC rc, List<T> targs, List<E> es, Src src) implements E{
    public Call{
      assert nonNull(e,name,rc,targs,src);
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