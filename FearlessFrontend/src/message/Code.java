package message;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Supplier;

import metaParser.Frame;
import metaParser.Message;
import tools.SourceOracle;

public enum Code{
  Unclosed,
  Unopened,
  UnexpectedToken,
  EndOfGroup,
  ExtraTokenInGroup,
  ProbeError,
  MissingSeparator,
  InterpolationNoClose,
  InterpolationNoOpen,
  WellFormedness,
  TypeError,
  ;  
  FearlessException of(BiFunction<SourceOracle,List<Frame>,String> f){ return new FearlessException(this, f); }
  FearlessException of(String msg){ return this.of((o,fs)->Message.of(o::loadString,fs,msg)); }
  FearlessException of(Supplier<String> msg){ return this.of((o,fs)->Message.of(o::loadString,fs,msg.get())); }
  
  public String toString(){
    return "Error "+this.ordinal()+" "+this.name();
  }
}