package message;

import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Supplier;

public enum Code{
  Unclosed,
  UnexpectedToken,
  EndOfGroup,
  ExtraTokenInGroup,
  
  Err2,//etc, of course with better names
  ;  
  public FearlessException of(BiFunction<SourceOracle,List<Frame>,List<Message>> f){ return new FearlessException(this, f); }
  public FearlessException of(String msg){ return this.of((o,fs)->Message.of(o,fs,msg)); }
  public FearlessException of(Supplier<String> msg){ return this.of((o,fs)->Message.of(o,fs,msg.get())); }
  
  public Message toMessage(){
    return new Message("Error "+this.ordinal()+"  "+this.name(),0);
  }
}