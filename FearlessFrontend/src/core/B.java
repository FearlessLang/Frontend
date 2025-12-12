package core;

import static offensiveUtils.Require.*;

import java.util.EnumSet;

import fearlessParser.RC;
import message.Join;
public record B(String x, EnumSet<RC> rcs){
  public B{ assert nonNull(x) && !rcs.isEmpty(); }
  public String toString(){
    return x+":"+Join.of(rcs.stream().map(rc->rc.name()),"",",","","");
  }
  public String compactToString(){
    var star = rcs.size() == 3 && rcs.contains(RC.imm) && rcs.contains(RC.mut) && rcs.contains(RC.read);
    var bs= rcs.size() == 6?"**":star?"*":Join.of(rcs.stream().map(rc->rc.name()),"",",","","");
    return x+":"+bs;
  }
}