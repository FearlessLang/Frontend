package inject;

import java.util.List;
import java.util.Optional;

import core.T;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;
import inference.IT;
import utils.Bug;

public class TypeRename{
  static List<IT.C> ofITC(List<IT.C> csi, List<String> xs, List<IT> ts){
    if (xs.isEmpty()){ return csi; }
    return csi.stream().map(c->of(c,xs,ts)).toList(); }
  static IT.C of(IT.C c, List<String> xs, List<IT> ts){
    if (xs.isEmpty()){ return c; }
    return new IT.C(c.name(), ofIT(c.ts(),xs,ts)); }
  static IT of(IT t, List<String> xs, List<IT> ts){
    assert xs.size() == ts.size();
    if (xs.isEmpty()){ return t; }
    return switch (t){
      case IT.X x -> getOrSame(x,x.name(),xs,ts);
      case IT.RCX(RC rc, var x) -> withRC(of(x,xs,ts),rc);
      case IT.RCC rcc -> rcc.withTs(ofIT(rcc.c().ts(),xs,ts));
      case IT.ReadImmX(var x) -> readImm(of(x,xs,ts));
      case IT.U u -> u;
      case IT.Err e -> e;
    };
  }
  static List<IT> ofIT(List<IT> tsi ,List<String> xs, List<IT> ts){
    if (xs.isEmpty()){ return tsi; }
    return tsi.stream().map(ti->of(ti,xs,ts)).toList(); }
  static List<Optional<IT>> ofITOpt(List<IT> tsi ,List<String> xs, List<IT> ts){ return tsi.stream().map(ti->Optional.of(of(ti,xs,ts))).toList(); }
  static List<Optional<IT>> ofOptITOpt(List<Optional<IT>> tsi ,List<String> xs, List<IT> ts){ return tsi.stream().map(ti->Optional.of(of(ti.get(),xs,ts))).toList(); }
  static IT readImm(IT t){return switch (t){
    case IT.X x -> new IT.ReadImmX(x);
    case IT.ReadImmX rix -> rix;
    case IT.RCX(RC rc, _) -> withRC(t,readImm(rc));
    case IT.RCC(RC rc, _) -> withRC(t,readImm(rc));
    case IT.U _   -> t;
    case IT.Err _ -> t;
  };}
  static IT withRC(IT t, RC rc){return switch (t){
    case IT.X x -> new IT.RCX(rc,x);
    case IT.ReadImmX _ -> throw Bug.unreachable();
    case IT.RCX(_, var x) -> new IT.RCX(rc,x);
    case IT.RCC(_, var c) -> new IT.RCC(rc, c);
    case IT.U _   -> throw Bug.unreachable();
    case IT.Err _ -> throw Bug.unreachable();
  };}

  static RC readImm(RC rc){ return rc == RC.imm || rc == RC.iso ? RC.imm: RC.read; }
  static <A> A getOrSame(A x, String name, List<String> xs, List<A> ts){
    var i= xs.indexOf(name); 
    return i == -1 ? x : ts.get(i);
  }
  public static List<IT.C> tcToITC(List<T.C> cs){ return cs.stream().map(TypeRename::tcToITC).toList(); }
  public static List<IT> tToIT(List<T> cs){ return cs.stream().map(TypeRename::tToIT).toList(); }
  public static List<T> itToT(List<IT> cs){ return cs.stream().map(TypeRename::itToT).toList(); }
  public static List<T> itOptToT(List<Optional<IT>> ts){ return ts.stream().map(ti->itToT(ti.get())).toList(); }
  
  public static T.C itcToTC(IT.C c){ return new T.C(c.name(),c.ts().stream().map(ti->itToT(ti)).toList()); }
  public static List<T.C> itcToTC(List<IT.C> cs){
    return cs.stream().map(TypeRename::itcToTC).toList();  
  }
  public static IT.C tcToITC(T.C c){
    return new IT.C(c.name(),c.ts().stream().map(ti->tToIT(ti)).toList());
  }
  public static IT tToIT(T t){return switch (t){
    case T.X(var name) -> new IT.X(name);
    case T.ReadImmX(var x) -> new IT.ReadImmX(new IT.X(x.name()));
    case T.RCX(var rc,var x) -> new IT.RCX(rc,new IT.X(x.name()));
    case T.RCC(var rc, var c) -> new IT.RCC(rc,tcToITC(c));
  };}
  public static T itToT(IT t){return switch (t){
    case IT.X(var name) -> new T.X(name);
    case IT.ReadImmX(var x) -> new T.ReadImmX(new T.X(x.name()));
    case IT.RCX(var rc,var x) -> new T.RCX(rc,new T.X(x.name()));
    case IT.RCC(var rc, var c) -> new T.RCC(rc,itcToTC(c));
    case IT.U _ -> throw Bug.of();// bug is good for testing, it will be replaced with this later: new T.RCC(RC.imm,new T.C(new TName("base.InferUnknown", 0, Pos.UNKNOWN), List.of()));
    case IT.Err _ ->new T.RCC(RC.imm,new T.C(new TName("base.InferErr", 0, Pos.UNKNOWN), List.of()));
  };}
  public static MSig normalizeHeaderBs(MSig header, inference.M.Sig sig){
    if (sig.bs().isEmpty()){ assert header.bs().isEmpty() : "header has generics but implementation has none: " + header + " / " + sig; return header; }
    var targetBs= sig.bs().get().stream().map(b -> b.x()).toList();
    if (header.bs().equals(targetBs)){ return header; }
    assert header.bs().size() == targetBs.size() : "generic arity mismatch header=" + header.bs() + " impl=" + targetBs;
    var fromXs= header.bs();
    var toITs= targetBs.stream().<IT>map(IT.X::new).toList();
    var renamedTs= ofIT(header.ts(), fromXs, toITs);
    var renamedRet= of(header.ret(), fromXs, toITs);
    return new MSig(header.rc(), targetBs, renamedTs, renamedRet);
  }
}