package fearlessParser;

import static org.junit.jupiter.api.Assertions.*;

import java.net.URI;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;

import message.FearlessErrFactory;
import metaParser.Span;

public class MiscTests {
  @Test void XIn_checks_Xs_not_xs(){
    var n = new Names(List.of("a"), List.of("X","Y"),List.of());
    assertTrue(n.XIn("X"));
    assertFalse(n.XIn("a"));
  }

  @Test void parseBack_afterFrontAlreadyConsumed_splitsWithinRemainingWindow(){
    var uri= URI.create("mem:/parseBackTest.fear");
    var span= new Span(uri,1,1,1,7);
    var a= new Token(TokenKind.LowercaseId,"a",1,1,List.of());
    var b= new Token(TokenKind.LowercaseId,"b",1,2,List.of());
    var c= new Token(TokenKind.LowercaseId,"c",1,3,List.of());
    var d= new Token(TokenKind.LowercaseId,"d",1,4,List.of());
    var e= new Token(TokenKind.LowercaseId,"e",1,5,List.of());
    var f= new Token(TokenKind.LowercaseId,"f",1,6,List.of());
    var p= new Parser(span,new Names(List.of(),List.of(),List.of()),List.of(a,b,c,d,e,f),new FearlessErrFactory());
    p.expectAny("");
    p.expectAny("");//front already consumed a,b: active window is now c,d,e,f
    var res= p.parseBack("back",false,
      pp->{ pp.expectAnyLast(""); pp.expectAnyLast(""); return 0; },
      pp->{ var out= new ArrayList<String>(); while(!pp.end()){ out.add(pp.expectAny("").content()); } return out; });
    assertEquals(List.of("e","f"), res.get());
    assertEquals(2, p.index());
    assertEquals(4, p.limit());
    assertEquals("c", p.expectAny("").content());
    assertEquals("d", p.expectAny("").content());
    assertTrue(p.end());
  }
}
