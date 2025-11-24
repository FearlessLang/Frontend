package core;

import static offensiveUtils.Require.*;
import java.util.List;
import java.util.Optional;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import inferenceCore.B;
import inferenceCore.T;
import fearlessParser.RC;
import files.Pos;
import inference.E;

public record M(Sig s, List<String> xs, Optional<E> e){
  public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T res, TName origin, Pos pos){
    public Sig{
      assert nonNull(rc,m,res,origin);
      assert unmodifiable(bs,"Sig.bs");
      assert unmodifiable(ts,"Sig.bs");
      assert eq(m.arity(),ts.size(),"Method name arity");
    }}
  public M{ assert nonNull(s,e); assert unmodifiable(xs,"M.xs"); }
}