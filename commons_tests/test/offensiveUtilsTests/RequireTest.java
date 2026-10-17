package offensiveUtilsTests;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.jupiter.api.Test;

import offensiveUtils.Require;

final class RequireTest{
  @Test void aModifiableListIsRefused(){
    assertThrows(AssertionError.class, () -> Require.unmodifiable(new ArrayList<>(List.of("a")), "list"));
  }
  @Test void aListOfCopiesIsUnmodifiable(){
    assertTrue(Require.unmodifiable(Collections.nCopies(2, "a"), "list"));
  }
  @Test void aReversedUnmodifiableListIsUnmodifiable(){
    assertTrue(Require.unmodifiable(List.of("a", "b").reversed(), "list"));
  }
}
