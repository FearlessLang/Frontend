package typeSystem;

import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;
import org.junit.jupiter.api.Test;

public class LubGlbTest{
  @Test void staticInitDoesNotFail(){
    Set<?> domain = RCLubGlb.domain();
    assertEquals(63, domain.size());
  }
}
