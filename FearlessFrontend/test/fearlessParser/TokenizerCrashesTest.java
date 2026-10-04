package fearlessParser;

import org.junit.jupiter.api.Test;

public class TokenizerCrashesTest extends testUtils.FearlessTestBase{
@Test void longBlockCommentIsOneToken(){
  var program= "A:{} /*"+"*a".repeat(50_000)+"*/ B:{}";
  org.junit.jupiter.api.Assertions.assertEquals(2, parseFull(program).decs().size());}
@Test void longUnclosedBlockCommentIsReportedAsUnclosed(){
  var program= "A:{} /*"+"a*".repeat(50_000)+" B:{}";
  parseFail("[###]While inspecting a block comment\nUnterminated block comment. Add \"*/\" to close it.\nError 2 UnexpectedToken\n", program);}
}
