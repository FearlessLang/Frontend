package fearlessParser;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;

import org.junit.jupiter.api.Test;

import core.FearlessException;
import tools.SourceOracle;

public class ParserInternalErrorsTest extends testUtils.FearlessTestBase{
  static void userError(String program){
    var fe= assertThrows(FearlessException.class, ()->Parse.from(SourceOracle.defaultDbgFearPath(0), program));
    var msg= fe.render(oracleRaw(List.of(program)));
    assertFalse(msg.contains("ProbeError"));
  }
  static void noEmptyFound(String program){
    var fe= assertThrows(FearlessException.class, ()->Parse.from(SourceOracle.defaultDbgFearPath(0), program));
    assertFalse(fe.render(oracleRaw(List.of(program))).contains("Found instead: \"\"."));
  }
@Test void groupFoundInsteadOfBoundColon(){ noEmptyFound("A[X[Y]]:{}"); }
@Test void groupFoundInsteadOfMethodBoundColon(){ noEmptyFound("A:{ .a[X[Y]]: A -> this }"); }
@Test void doubleSemicolonAfterMethod(){ userError("A:{ .a: A -> this;; }"); }
@Test void leadingSemicolonInTypeDeclaration(){ userError("A:{ ; .a: A -> this }"); }
@Test void onlySemicolonInObjectLiteral(){ userError("A:{ .a: A -> {;} }"); }
}
