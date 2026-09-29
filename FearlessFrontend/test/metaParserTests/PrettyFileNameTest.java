package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.net.URI;
import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import metaParser.PrettyFileName;

public class PrettyFileNameTest{
  static final Path cwd= Path.of("").toAbsolutePath();
  static void same(String uri){ assertEquals(uri, PrettyFileName.displayFileName(URI.create(uri))); }
  @Test void fearUriVerbatim(){ same("fear:/_pkb/_rank_app200.fear"); }
  @Test void longUriNotTruncated(){ same("fear:/"+"a/".repeat(60)+"b.fear"); }
  @Test void underCwdIsRelative(){
    var p= cwd.resolve("src").resolve("a.fear");
    assertEquals(Path.of("src","a.fear").toString(), PrettyFileName.displayFileName(p.toUri()));
  }
  @Test void cwdItselfIsAbsolute(){ assertEquals(cwd.toString(), PrettyFileName.displayFileName(cwd.toUri())); }
  @Test void outsideCwdIsAbsolute(){
    var p= cwd.getRoot().resolve("zzOutside").resolve("a.fear");
    assertEquals(p.toString(), PrettyFileName.displayFileName(p.toUri()));
  }
  @Test void spaceIsEscaped(){
    var p= cwd.resolve("my dir").resolve("a.fear");
    assertEquals(p.toUri().toASCIIString(), PrettyFileName.displayFileName(p.toUri()));
  }
  @Test void nonAsciiIsEscaped(){
    var p= cwd.resolve("café.fear");
    assertEquals(p.toUri().toASCIIString(), PrettyFileName.displayFileName(p.toUri()));
  }
  @Test void nonAsciiFearUriIsEscaped(){
    assertEquals("fear:/caf%C3%A9.fear", PrettyFileName.displayFileName(URI.create("fear:/café.fear")));
  }
}
