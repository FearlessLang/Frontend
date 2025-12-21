package fearlessFullGrammar;

import static offensiveUtils.Require.*;
import java.util.List;

import core.RC;

public record B(T.X x, BT bt){//Span of T.X x needed in crucial error
  public B{ assert nonNull(x,bt);}
  public sealed interface BT{}
  public record Star() implements BT{}
  public record StarStar() implements BT{}
  public record RCS(List<RC> rcs) implements BT{
    public RCS{ assert unmodifiable(rcs,"B.rcs"); }//if rcs is empty, it means absence of :RCs
  }
}