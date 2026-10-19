package compact;
import static compact.Util.*;
import compact.Frontend.*;
import compact.Frontend.T.*;
import java.util.*;
import java.util.stream.*;
public final class Print{
  public static String lines(List<Literal> ls){ return join(ls, "", "\n",""); }
  static String join(Collection<?> l,String start,String sep,String end){ return l.size()==0? "" : l.stream().map(Print::of).collect(Collectors.joining(sep,start,end)); }
  static String r(RC r){ return r == RC.imm ? "" : r+" "; }
  public static String of(Object o){ return switch(o){
    case MName m -> m.s(); case B b -> b.x()+":"+join(b.caps(), "", ",",""); case X x -> x.name();
    case RX(var r,var x)-> r.name()+" "+x.name(); case RI(var x)-> "read/imm "+x.name(); case U _ -> "?";
    case C c -> c.name().s()+join(c.types(), "[", ",", "]"); case R(var r,var c)-> (r == null ?"AnyRC ": r(r))+of(c);
    case E.X x -> x.name(); case E.Type t -> of(t.type());
    case E.Call c -> of(c.e())+of(c.name())+"["+c.r()+join(c.y(),",", ",", "")+"]"+join(c.es(),"(",", ", ")");
    case Literal l -> l.r()+" "+l.name().s()+join(l.b(), "[", ",", "]")+":"+join(l.cs(), "", ", ","")+"{'"+l.self()+" "+join(l.ms(), "", "; ","")+"}";
    case M m -> r(m.s().r())+of(m.s().m())+join(m.s().b(), "[", ",", "]")+join(zip(m.v(),m.s().types(),(x,t)-> x+":"+of(t)), "(",", ", ")")
      +":"+of(m.s().t())+(m.e()== null ? "" : "->"+of(m.e()));
    default -> o.toString(); };}
}
