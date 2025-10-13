package fearlessFullGrammar;

import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.EnumSet;
import java.util.List;

import fearlessParser.RC;

public record B(T.X x, BT bt){
  public B{ assert nonNull(x,bt);}
  public sealed interface BT{}
  public record Star() implements BT{}
  public record StarStar() implements BT{}
  public record RCS(List<RC> rcs) implements BT{
    public RCS{//if rcs is empty, it means absence of :RCs
      assert unmodifiable(rcs,"B.rcs");
      assert rcs.isEmpty() || rcs.equals(List.copyOf(EnumSet.copyOf(rcs)));//check the order is normalized  
    }
  }
}