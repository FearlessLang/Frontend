package typeSystem;

import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

import core.RC;
import utils.OneOr;

public final class RCLubGlb{
  private RCLubGlb(){}
  private static final HashMap<Set<RC>,RC> lubMap= new HashMap<>();
  private static final HashMap<Set<RC>,RC> glbMap= new HashMap<>();
  public static Set<Set<RC>> domain(){ return Collections.unmodifiableSet(lubMap.keySet()); }
  public static RC lub(EnumSet<RC> options){ return Objects.requireNonNull(lubMap.get(options)); }
  public static RC glb(EnumSet<RC> options){ return Objects.requireNonNull(glbMap.get(options)); }
  static {
    for (var mask= 1; mask < 1 << RC.values().length; mask++){
      var options= EnumSet.noneOf(RC.class);
      for (var rc : RC.values()){ if ((mask >> rc.ordinal() & 1) == 1){ options.add(rc); } }
      var ubs= Stream.of(RC.values()).filter(ub->options.stream().allMatch(x->x.isSubType(ub))).toList();
      var lbs= Stream.of(RC.values()).filter(lb->options.stream().allMatch(lb::isSubType)).toList();
      lubMap.put(options, OneOr.of("lub",ubs.stream().filter(u->ubs.stream().allMatch(u::isSubType))));
      glbMap.put(options, OneOr.of("glb",lbs.stream().filter(l->lbs.stream().allMatch(x->x.isSubType(l)))));
    }
  }}
