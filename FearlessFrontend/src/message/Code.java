package message;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Supplier;

import metaParser.Frame;
import metaParser.Message;

public enum Code{
  Unclosed,
  Unopened,
  UnexpectedToken,
  EndOfGroup,
  ExtraTokenInGroup,
  ProbeError,
  MissingSeparator,
  
  Err2,//etc, of course with better names
  ;  
  public FearlessException of(BiFunction<SourceOracle,List<Frame>,String> f){ return new FearlessException(this, f); }
  public FearlessException of(String msg){ return this.of((o,fs)->Message.of(o::loadString,fs,msg)); }
  public FearlessException of(Supplier<String> msg){ return this.of((o,fs)->Message.of(o::loadString,fs,msg.get())); }
  
  public String toString(){
    return "Error "+this.ordinal()+"  "+this.name();
  }
}