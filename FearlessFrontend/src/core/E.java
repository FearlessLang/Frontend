package core;

import files.Pos;
import inferenceCore.B;
import inferenceCore.T;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.*;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;

public sealed interface E {
  Pos pos();
  record X(String name, Pos pos) implements E{
    public X{ assert validate(name, "parameter name",LowercaseId); }}
  record Type(T.RCC type, Pos pos) implements E{
    public Type{ assert nonNull(type,pos); }}
  record Literal(RC rc, TName name, List<B> bs, List<T.C> cs, String thisName, List<M> ms, Pos pos) implements E{
    public Literal{
      assert unmodifiable(bs,"L.bs");
      assert unmodifiable(cs,"L.cs");
      assert unmodifiable(ms, "L.ms");
      assert nonNull(rc,name,thisName,pos);
    }
  }
  record Call(E e, MName name, RC rc, List<T> targs, List<E> es, Pos pos) implements E{
    public Call{
      assert nonNull(e,name,rc,targs,pos);
      assert unmodifiable(es, "E.Call.es");
      assert unmodifiable(targs, "E.Call.targs");
    }
  }
}