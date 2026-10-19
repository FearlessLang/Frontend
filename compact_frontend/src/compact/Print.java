package compact;
import static compact.Util.*;
import compact.Frontend.*;
import compact.Frontend.IT.*;
import java.util.*;
import java.util.stream.*;
public final class Print{
  public static String lines(List<Literal> ls){ return join(ls, "", "\n",""); }
  static String join(Collection<?> l,String start,String sep,String end){ return l.isEmpty()? "" : l.stream().map(Print::of).collect(Collectors.joining(sep,start,end)); }
  static String rc(RC rc){ return rc == RC.imm ? "" : rc+" "; }
  public static String of(Object o){ return switch(o){
    case MName m -> m.s(); case B b -> b.x()+":"+join(b.rcs(), "", ",",""); case X x -> x.name();
    case RCX(var rc,var x)-> rc.name()+" "+x.name(); case ReadImmX(var x)-> "read/imm "+x.name(); case U _ -> "?";
    case C c -> c.name().s()+join(c.ts(), "[", ",", "]"); case RCC(var rc,var c)-> (rc == null ?"AnyRC ": rc(rc))+of(c);
    case IE.X x -> x.name(); case IE.Type t -> of(t.type());
    case IE.Call c -> of(c.e())+of(c.name())+"["+c.rc()+join(c.targs(),",", ",", "")+"]"+join(c.es(),"(",", ", ")");
    case Literal l -> l.rc()+" "+l.name().s()+join(l.bs(), "[", ",", "]")+":"+join(l.cs(), "", ", ","")+"{'"+l.self()+" "+join(l.ms(), "", "; ","")+"}";
    case IM m -> rc(m.sig().rc())+of(m.sig().m())+join(m.sig().bs(), "[", ",", "]")+join(zip(m.xs(),m.sig().ts(),(x,t)-> x+":"+of(t)), "(",", ", ")")
      +":"+of(m.sig().ret())+(m.e()== null ? "" : "->"+of(m.e()));
    default -> o.toString(); };}
}
