package typeSystem;

import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;
import org.junit.jupiter.api.Test;

class LubGlbTest {
  @Test void staticInitDoesNotFail(){
    Set<?> domain = RCLubGlb.domain();
    assertEquals(63, domain.size());
  }
}
