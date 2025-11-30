package core;

import static offensiveUtils.Require.*;

import java.util.List;

import fearlessParser.RC;
import message.Join;
public record B(String x, List<RC> rcs){//TODO: should rcs be an EnumSet? if so search for all EnumSet.copyOf to simplify code
  public B{ assert nonNull(x) && unmodifiableDistinct(rcs,"B.rcs") && !rcs.isEmpty(); }
  public String toString(){
    return x+":"+Join.of(rcs.stream().map(rc->rc.name()),"",",","","");
  }
}