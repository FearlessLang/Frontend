package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import tools.Utf8Sink;

final class Utf8SinkTest{
  @Test void closingTwiceDoesNothing(){
    var out= new StringBuilder();
    var sink= new Utf8Sink(out::append);
    sink.write(new byte[]{'a', (byte)0xC3}, 0, 2);
    sink.close();
    assertEquals("a�", out.toString());
    sink.close();
    assertEquals("a�", out.toString());
  }
}
