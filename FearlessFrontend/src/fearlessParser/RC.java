package fearlessParser;

import java.util.List;

import core.B;
import utils.OneOr;

public enum RC {
  imm, mut, read, iso, mutH, readH;
  public boolean isSubType(RC other){ //this <= other
    if (this == other){ return true; }
    if (other== RC.readH) { return true; }
    return switch (this){
      case mut -> other == RC.mutH || other == RC.read;
      case imm -> other == RC.read;
      case iso -> true;
      case readH, read, mutH -> false;
    };
  }
  public RC isoToMut(){ return this == iso? mut : this; }
  public RC readImm(){ return (this == iso || this == imm ) ? imm : read; }
  public static B get(List<B> bs, String name){
    return OneOr.of("Type variable not found",bs.stream().filter(b->b.x().equals(name)));
  }
 
}