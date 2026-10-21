package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.net.URI;
import java.util.List;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Test;

import metaParser.Frame;
import metaParser.Message;
import metaParser.Span;

public final class MessageTest{
  private static final URI file= URI.create("fear:/a.fear");
  private static String nested(int count){
    List<Frame> frames= IntStream.range(0, count).mapToObj(i -> new Frame("f"+i, new Span(file, 1, 5-i, 1, 5+i))).toList();
    return Message.of(_ -> "abcdefghij\n", frames, "msg");
  }
  @Test void fiveNestedSpansOnOneLineShowOnlyTheThreeInnermost(){
    assertEquals("""
      In file: fear:/a.fear

      001| abcdefghij
         |   -~^~-

      While inspecting f0 > f1 > f2 > f3 > f4
      msg""", nested(5));
  }
  @Test void threeNestedSpansOnOneLineShowAllThree(){
    assertEquals("""
      In file: fear:/a.fear

      001| abcdefghij
         |   -~^~-

      While inspecting f0 > f1 > f2
      msg""", nested(3));
  }
}
