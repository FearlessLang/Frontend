package inferenceGrammar;

import static offensiveUtils.Require.nonNull;
import static offensiveUtils.Require.unmodifiable;

import java.util.List;

import fearlessParser.RC;

public record B(T.X x, List<RC> rcs){
  public B{ assert nonNull(x) && unmodifiable(rcs,"B.rcs") && !rcs.isEmpty(); }
}