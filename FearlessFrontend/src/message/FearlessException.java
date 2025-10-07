package message;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.BiFunction;

import metaParser.Frame;
import metaParser.HasFrames;

public final class FearlessException extends RuntimeException implements HasFrames<FearlessException>{
  private static final long serialVersionUID = 1L;
  private final Code code;
  private final ArrayList<Frame> frames= new ArrayList<>();
  private final BiFunction<SourceOracle,List<Frame>,String> msgFactory;
  public FearlessException(Code code, BiFunction<SourceOracle,List<Frame>,String> f){
    super(code.toString());
    this.code = Objects.requireNonNull(code);
    this.msgFactory = Objects.requireNonNull(f);
  }
  public Code code(){ return code; }
  public String render(SourceOracle env){
    var msg= msgFactory.apply(env,Collections.unmodifiableList(frames));
    if (msg.endsWith("\n")){ return msg + code; }
    return msg + "\n" + code;
  }
  @Override public FearlessException addFrame(Frame f){ frames.add(f); return this; }
}