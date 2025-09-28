package message;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.BiFunction;

import metaParser.Frame;
import metaParser.HasFrames;
import metaParser.Message;
import utils.Push;

public final class FearlessException extends RuntimeException implements HasFrames{
  private static final long serialVersionUID = 1L;
  private final Code code;
  private final ArrayList<Frame> frames= new ArrayList<>();
  private final BiFunction<SourceOracle,List<Frame>,List<Message>> msgFactory;
  public FearlessException(Code code, BiFunction<SourceOracle,List<Frame>,List<Message>> f){
    super(code.toString());
    this.code = Objects.requireNonNull(code);
    this.msgFactory = Objects.requireNonNull(f);
  }
  public Code code(){ return code; }
  public List<Message> render(SourceOracle env){
    return Push.of(msgFactory.apply(env,Collections.unmodifiableList(frames)),code.toMessage());
  }
  @Override public void addFrame(Frame f){ frames.add(f); }
}