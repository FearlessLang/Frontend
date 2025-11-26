package core;

import java.util.List;
import java.util.stream.Collectors;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;

public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, TName origin, boolean abs, Pos pos){
  public String toString(){
    var bsS= bs.isEmpty()?"":"["+bs.stream().map(Object::toString).collect(Collectors.joining(","))+"]";
    var tsS= ts.isEmpty() ? "" : "("+ts.stream().map(Object::toString).collect(Collectors.joining(","))+")";
    var rcS= rc==RC.imm?"":rc.toString()+" ";      
    var ori= "@"+origin.s();      
    var mS= m.toString();
    return " "+rcS+mS+bsS+tsS+":"+ret+ori+";";
  }
}