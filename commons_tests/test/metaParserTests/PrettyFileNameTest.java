package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.net.URI;

import org.junit.jupiter.api.Test;

import metaParser.PrettyFileName;

public final class PrettyFileNameTest{
  static void same(String uri){ assertEquals(uri, PrettyFileName.displayFileName(URI.create(uri))); }
  static void shows(String expected, String uri){ assertEquals(expected, PrettyFileName.displayFileName(URI.create(uri))); }
  @Test void fearUriVerbatim(){ same("fear:/_pkb/_rank_app200.fear"); }
  @Test void longUriNotTruncated(){ same("fear:/"+"a/".repeat(60)+"b.fear"); }
  @Test void fileUriVerbatim(){ same("file:///C:/data/src/a.fear"); }
  @Test void escapesStayVerbatim(){ same("file:///home/my%20dir/caf%C3%A9.fear"); }
  @Test void nonAsciiIsEscaped(){ shows("fear:/caf{U+00E9}.fear", "fear:/caf\u00e9.fear"); }
  @Test void beyondBmpIsEscaped(){ shows("fear:/{U+01F600}.fear", "fear:/\ud83d\ude00.fear"); }
  @Test void loneSurrogateIsEscaped(){ shows("fear:/a{U+D800}.fear", "fear:/a\ud800.fear"); }
  @Test void sanitizeEscapesTheEscapeChar(){ assertEquals("a{U+007B}b} {U+00E9}{U+0009}", PrettyFileName.sanitizeAscii("a{b} \u00e9\t")); }
}
