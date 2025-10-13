package fearlessParser;

import static org.junit.jupiter.api.Assertions.*;

import java.util.List;
import org.junit.jupiter.api.Test;

public class MiscTests {
  @Test void XIn_checks_Xs_not_xs(){
    var n = new Names(List.of("a"), List.of("X","Y"),List.of());
    assertTrue(n.XIn("X"));
    assertFalse(n.XIn("a"));
  }

}
