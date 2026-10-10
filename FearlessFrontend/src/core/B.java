package core;

import static offensiveUtils.Require.*;

import java.util.EnumSet;
import java.util.List;

import utils.Join;
import utils.OneOr;

public record B(String x, EnumSet<RC> rcs){
  public B{ assert nonNull(x); assert !rcs.isEmpty(); }
  public static List<String> xs(List<B> bs){ return bs.stream().map(B::x).toList(); }
  public static B get(List<B> bs, String name){
    return OneOr.of("Type variable not found",bs.stream().filter(b->b.x().equals(name)));
  }
  public String toString(){
    return x+":"+Join.of(rcs.stream().map(RC::name),"",",","","");
  }
  public String compactToString(){
    if (rcs.equals(EnumSet.allOf(RC.class))){ return x+":**"; }
    if (rcs.equals(EnumSet.of(RC.imm,RC.mut,RC.read))){ return x+":*"; }
    return toString();
  }
}