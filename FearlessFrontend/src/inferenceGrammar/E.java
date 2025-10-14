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
  record X(String name, IT t, Pos pos) implements E{
    public X{ assert nonNull(t) && validate(name, "parameter name",LowercaseId); }
    public String toString(){ return name+":"+t; }
  }
  record Literal(String thisName, List<Sig> sigs, List<Impl> impls, IT t, Pos pos) implements E{
    public Literal{
      assert unmodifiable(sigs, "L.sigs");
      assert unmodifiable(impls, "L.impls");
      assert nonNull(thisName,t);
    }
    public String toString(){ return "{`"+thisName
      + sigs.stream().map(Object::toString).collect(Collectors.joining(";"))
      + impls.stream().map(Object::toString).collect(Collectors.joining(";"))
      +"}:"+t; }
  }
  record Call(E e, MName name, Optional<RC> rc, List<IT> targs, List<E> es, IT t, Pos pos) implements E{
    public Call{
      assert nonNull(e,name,rc,targs,t);
      assert unmodifiable(es, "E.Call.es");
    }
    public String toString(){ return ""+e+name+"["+rc+","
      +targs.stream().map(Object::toString).collect(Collectors.joining(","))+"]("
      +es.stream().map(Object::toString).collect(Collectors.joining(","))+"):"+t;
    }
  }
  record ICall(E e, MName name, List<E> es, IT t, Pos pos) implements E{
    public String toString(){ return ""+e+name+"("
        +es.stream().map(Object::toString).collect(Collectors.joining(","))+"):"+t;
      }
  }
  record Type(T.RCC type, IT t, Pos pos) implements E{
    public String toString(){ return ""+type+":"+t; }
  }
}