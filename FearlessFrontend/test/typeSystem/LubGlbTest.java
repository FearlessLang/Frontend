package typeSystem;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

public class LubGlbTest{
  @Test void staticInitDoesNotFail(){
    var domain= RCLubGlb.domain();
    assertEquals(63, domain.size());
  }
}
