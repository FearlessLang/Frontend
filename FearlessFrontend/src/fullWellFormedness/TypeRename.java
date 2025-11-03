package fullWellFormedness;

import java.util.List;
import java.util.Optional;
import fearlessParser.RC;
import inferenceGrammar.IT;
import inferenceGrammar.T;
import utils.Bug;

public class TypeRename{
  static List<T.C> ofTC(List<T.C> csi, List<String> xs, List<T> ts){ return csi.stream().map(c->of(c,xs,ts)).toList(); }
  static T.C of(T.C c, List<String> xs, List<T> ts){ return new T.C(c.name(), ofT(c.ts(),xs,ts)); }
  static IT of(IT t, List<String> xs, List<IT> ts){ return switch(t){
    case IT.X x -> getOrSame(x,x.name(),xs,ts);
    case IT.RCX(RC rc, var x) -> withRC(of(x,xs,ts),rc);
    case IT.RCC(RC rc, var c) -> new IT.RCC(rc,new IT.C(c.name(),ofIT(c.ts(),xs,ts)));
    case IT.ReadImmX(var x) -> readImm(of(x,xs,ts));
    case IT.U _ -> throw Bug.unreachable();
    case IT.Err _ -> throw Bug.unreachable();
  };}
  static T of(T t, List<String> xs, List<T> ts){ return switch(t){
    case T.X x -> getOrSame(x,x.name(),xs,ts);
    case T.RCX(RC rc, var x) -> withRC(of(x,xs,ts),rc);
    case T.RCC(RC rc, var c) -> new T.RCC(rc,new T.C(c.name(),ofT(c.ts(),xs,ts)));
    case T.ReadImmX(var x) -> readImm(of(x,xs,ts));
  };}
  static fearlessFullGrammar.T of(fearlessFullGrammar.T t, List<String> xs, List<fearlessFullGrammar.T> ts){ return switch(t){
    case fearlessFullGrammar.T.X x -> getOrSame(x,x.name(),xs,ts);
    case fearlessFullGrammar.T.RCX(RC rc, var x) -> withRC(of(x,xs,ts),rc);
    case fearlessFullGrammar.T.RCC(var rc, var c) -> new fearlessFullGrammar.T.RCC(rc,new fearlessFullGrammar.T.C(c.name(),c.ts().map(tsi->ofFT(tsi,xs,ts))));
    case fearlessFullGrammar.T.ReadImmX(var x) -> readImm(of(x,xs,ts));
  };}
  static List<IT> ofIT(List<IT> tsi ,List<String> xs, List<IT> ts){ return tsi.stream().map(ti->of(ti,xs,ts)).toList(); }
  static List<T> ofT(List<T> tsi, List<String> xs, List<T> ts){ return tsi.stream().map(ti->of(ti,xs,ts)).toList(); }
  static List<fearlessFullGrammar.T> ofFT(List<fearlessFullGrammar.T> tsi, List<String> xs, List<fearlessFullGrammar.T> ts){ return tsi.stream().map(ti->of(ti,xs,ts)).toList(); }
  static IT readImm(IT t){return switch(t){
    case IT.X x -> new IT.ReadImmX(x);
    case IT.ReadImmX rix -> rix;
    case IT.RCX(RC rc, _) -> withRC(t,readImm(rc));
    case IT.RCC(RC rc, _) -> withRC(t,readImm(rc));
    case IT.U _   -> throw Bug.unreachable();
    case IT.Err _ -> throw Bug.unreachable();
  };}
  static T readImm(T t){return switch(t){
    case T.X x -> new T.ReadImmX(x);
    case T.ReadImmX rix -> rix;
    case T.RCX(RC rc, _) -> withRC(t,readImm(rc));
    case T.RCC(RC rc, _) -> withRC(t,readImm(rc));
  };}
  static fearlessFullGrammar.T readImm(fearlessFullGrammar.T t){return switch(t){
    case fearlessFullGrammar.T.X x -> new fearlessFullGrammar.T.ReadImmX(x);
    case fearlessFullGrammar.T.ReadImmX rix -> rix;
    case fearlessFullGrammar.T.RCX(RC rc, _) -> withRC(t,readImm(rc));
    case fearlessFullGrammar.T.RCC(var rc, _) -> withRC(t,readImm(rc.orElse(RC.imm)));
  };}
  static IT withRC(IT t, RC rc){return switch(t){
    case IT.X x -> new IT.RCX(rc,x);
    case IT.ReadImmX _ -> throw Bug.unreachable();
    case IT.RCX(_, var x) -> new IT.RCX(rc,x);
    case IT.RCC(_, var c) -> new IT.RCC(rc, c);
    case IT.U _   -> throw Bug.unreachable();
    case IT.Err _ -> throw Bug.unreachable();
  };}
  static T withRC(T t, RC rc){return switch(t){
    case T.X x -> new T.RCX(rc,x);
    case T.ReadImmX _ -> throw Bug.unreachable();
    case T.RCX(_, var x) -> new T.RCX(rc,x);
    case T.RCC(_, var c) -> new T.RCC(rc, c);
  };}
  static fearlessFullGrammar.T withRC(fearlessFullGrammar.T t, RC rc){return switch(t){
    case fearlessFullGrammar.T.X x -> new fearlessFullGrammar.T.RCX(rc,x);
    case fearlessFullGrammar.T.ReadImmX _ -> throw Bug.unreachable();
    case fearlessFullGrammar.T.RCX(_, var x) -> new fearlessFullGrammar.T.RCX(rc,x);
    case fearlessFullGrammar.T.RCC(_, var c) -> new fearlessFullGrammar.T.RCC(Optional.of(rc), c);
  };}
  static RC readImm(RC rc){ return rc == RC.imm || rc == RC.iso ? RC.imm: RC.read; }
  static <A> A getOrSame(A x, String name,List<String> xs, List<A> ts){
    var i= xs.indexOf(name); 
    return i == -1 ? x : ts.get(i);
  }
  public static IT tToIT(inferenceGrammar.T t){return switch(t){
    case inferenceGrammar.T.X(var name) -> new IT.X(name);
    case inferenceGrammar.T.ReadImmX(var x) -> new IT.ReadImmX(new IT.X(x.name()));
    case inferenceGrammar.T.RCX(var rc,var x) -> new IT.RCX(rc,new IT.X(x.name()));
    case inferenceGrammar.T.RCC(var rc, var c) -> new IT.RCC(rc,new IT.C(c.name(),
      c.ts().stream().map(ti->tToIT(ti)).toList()));
  };}
}