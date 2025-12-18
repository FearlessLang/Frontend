package core;

import java.util.List;

import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessFullGrammar.TSpan;
import fearlessParser.RC;
import message.Join;

public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, TName origin, boolean abs, TSpan span){
  public String toString(){
    var bsS= Join.of(bs,"[",",","]","");
    var tsS= Join.of(ts,"(",",",")","");
     
    var ori= "@"+origin.s();      
    var mS= m.toString();
    return " "+rc.toStrSpace()+mS+bsS+tsS+":"+ret+ori+";";
  }
}