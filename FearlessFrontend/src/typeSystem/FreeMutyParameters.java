package typeSystem;

import java.util.List;
import core.B;
import core.E;
import core.M;
import core.RC;
import core.T;
interface CaptureWalk{
  List<B> bs();
  Gamma g();
  boolean isFree(RC rc);
  default boolean isFree(E e){
    return switch (e){
      case E.Literal l -> isFree(l);
      case E.Call c -> isFree(c);
      case E.Type _ -> true;
      case E.X x -> isFree(x);
    };
  }
  default boolean isFree(E.Literal l){ return l.ms().stream().allMatch(this::isFree); }
  private boolean isFree(M m){
    //NOTE: we could be more permissive skipping m.sig().rc() == RC.imm
    //but is not that obvious. iso {imm .foo->captMut} fails but
    //mut {imm .foo->captMut} may pass. The same reason we can skip imm methods is reason to 
    //not promote mut->iso? 
    return m.e().stream().allMatch(this::isFree);
  }
  private boolean isFree(E.Call c){
    return isFree(c.e()) && c.es().stream().allMatch(this::isFree);
  }
  private boolean isFree(T t){
    return switch (t){
      case T.X(String name, _) -> RC.get(bs(), name).rcs().stream().allMatch(this::isFree);
      case T.RCX(RC rc, _) -> isFree(rc);
      case T.ReadImmX(T.X x) -> isFree(x);
      case T.RCC(RC rc,_,_) -> isFree(rc);
    };
  }
  default boolean isFree(E.X x){
    var cur= g()._bindOrNull(x.name());
    if (cur == null){ return true; }
    if (!(cur.current() instanceof Change.WithT w)){ return true; }
    return isFree(w.currentT());
  }
}
public record FreeMutyParameters(List<B> bs,Gamma g) implements CaptureWalk{
  public boolean isFree(RC rc){ return rc == RC.iso || rc == RC.imm; }
}
record ImmCaptures(List<B> bs,Gamma g) implements CaptureWalk{
  public boolean isFree(RC rc){ return rc == RC.imm; }
}