package core;

import static offensiveUtils.Require.*;

import java.util.List;
import java.util.stream.Collectors;

import fearlessParser.RC;
public record B(String x, List<RC> rcs){
  public B{ assert nonNull(x) && unmodifiableDistinct(rcs,"B.rcs") && !rcs.isEmpty(); }
  public String toString(){
    return x+":"+rcs.stream().map(rc->rc.name()).collect(Collectors.joining(","));
  }
}