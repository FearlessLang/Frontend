package compact;
import static compact.Util.*;
import compact.Frontend.*;
import compact.Frontend.T.*;
import java.util.*;
import java.util.stream.*;
public final class Print{
  public static String lines(List<Literal>ls){return join(ls,"\n");}
  static String join(Collection<?>l,String sep){return l.stream().map(Print::of).collect(Collectors.joining(sep));}
  static String wrap(Collection<?>l,String ends,String sep){return l.isEmpty()?"":ends.charAt(0)+join(l,sep)+ends.charAt(1);}
  static String square(Collection<?>l){return wrap(l,"[]",",");}
  static String r(RC r){return r==RC.imm?"":r+" ";}
  public static String of(Object o){return switch(o){
    case MN(var s,_)->s;
    case B(var x,var cs)->x+":"+join(cs,",");
    case X(var x)->x;
    case RX(var r,X(var x))->r+" "+x;
    case RI(X(var x))->"read/imm "+x;
    case U _->"?";
    case C(var n,var ts)->n.s()+square(ts);
    case R(var r,var c)->(r==null?"AnyRC ":r(r))+of(c);
    case E.X(var x,_)->x;
    case E.Call(var e,var n,var r,var y,var es,_,_)->of(e)+of(n)+"["+r+(y.isEmpty()?"":","+join(y,","))+"]"+wrap(es,"()",", ");
    case Literal(var r,var n,var b,var cs,var self,var ms,_,_,_)->r+" "+n.s()+square(b)+":"+join(cs,", ")+"{'"+self+" "+join(ms,"; ")+"}";
    case M(var s,var v,var e)->r(s.r())+of(s.m())+square(s.b())+wrap(zip(v,s.types(),(x,t)->x+":"+of(t)),"()",", ")+":"+of(s.t())+(e==null?"":"->"+of(e));
    default->o.toString();
  };}
}
