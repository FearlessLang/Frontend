package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.net.URI;
import java.util.Collection;
import java.util.List;

import org.junit.jupiter.api.Test;

import metaParser.ErrFactory;
import metaParser.ErrFactory.LikelyCause;
import metaParser.Frame;
import metaParser.HasFrames;
import metaParser.Layout;
import metaParser.MetaParser;
import metaParser.MetaTokenizer;
import metaParser.Span;
import metaParser.Token;
import metaParser.TokenKind;
import metaParser.TokenMatch;

public final class LayoutTest{
  enum K implements TokenKind{
    Sof("(?!)"), Eof("(?!)"), Lb("\\{"), Rb("\\}"), Ws("\\s+");
    final TokenMatch m;
    K(String r){ m= TokenMatch.fromRegex(r); }
    @Override public TokenMatch matcher(){ return m; }
    @Override public int priority(){ return 0; }
  }
  record Tok(K kind, String content, int line, int column, List<Tok> tokens) implements Token<Tok,K>{
    @Override public String toString(){ return kind+" "+line+":"+column; }
  }
  @SuppressWarnings("serial")
  static final class Ex extends RuntimeException implements HasFrames<Ex>{
    final Span at;
    Ex(String name, Span at){ super(name); this.at= at; }
    @Override public Ex addFrame(Frame f){ return this; }
  }
  static final class Tz extends MetaTokenizer<Tok,K,Ex,Tz,Ps,Ef>{
    @Override public Tz self(){ return this; }
    @Override public Tok make(K kind, String text, int line, int col, List<Tok> tokens){ return new Tok(kind, text, line, col, tokens); }
  }
  static final class Ps extends MetaParser<Tok,K,Ex,Tz,Ps,Ef>{
    Ps(Span s, List<Tok> ts){ super(s, ts); }
    @Override public Ps self(){ return this; }
    @Override public boolean skip(Tok t){ return t.is(K.Sof, K.Eof); }
    @Override public Ps make(Span s, List<Tok> ts){ return new Ps(s, ts); }
    @Override public Ef errFactory(){ return new Ef(); }
  }
  static final class Ef implements ErrFactory<Tok,K,Ex,Tz,Ps,Ef>{
    @Override public Ex illegalCharAt(Span at, int cp, Tz tz){ return new Ex("illegalChar", at); }
    @Override public Ex unrecognizedTextAt(Span at, String what, Tz tz){ return new Ex("unrecognized", at); }
    @Override public Ex groupHalt(Tok open, Tok stop, Collection<K> closers, LikelyCause likely, Tz tz){ return new Ex("groupHalt", null); }
    @Override public Ex eatenCloserBetween(Tok open, Tok stop, Collection<K> closers, Tok frag, Tok container, Tz tz){ return new Ex("eatenCloser", null); }
    @Override public Ex eatenOpenerBetween(Tok open, Tok stop, Collection<K> closers, Tok frag, Tok container, Tz tz){ return new Ex("eatenOpener", null); }
    @Override public Ex missing(Span at, String what, List<K> expected, Ps p){ return new Ex("missing", at); }
    @Override public Ex missingButFound(Span at, String what, Tok found, Collection<K> expected, Ps p){ return new Ex("missingButFound", at); }
    @Override public Ex extraContent(Span from, String what, Collection<K> expected, Ps p){ return new Ex("extraContent", from); }
    @Override public Ex probeStalledIn(String label, Span at, int s, int e, Ps p){ return new Ex("probeStalled", at); }
    @Override public Ex badProbeDropIn(String label, Span at, int s, int e, int drop, Ps p){ return new Ex("badProbeDrop", at); }
  }
  static final URI file= URI.create("fear:/a.fear");
  static final Layout layout= new Layout(){
    @Override public int line(int line){ return line == 1 ? 7 : 9; }
    @Override public int column(int line, int column){ return line == 1 ? column + 4 : 3; }
  };
  static Tz tokenizer(String src){
    return new Tz()
      .tokenKinds(List.of(K.Lb, K.Rb, K.Ws), K.Sof, K.Eof)
      .input(file, src)
      .layout(layout)
      .setErrFactory(new Ef());
  }
  @Test void tokensAndTheSpanOfTheTextGoThroughTheLayout(){
    var tz= tokenizer("{ {\n}}").tokenize();
    assertEquals("[Sof 7:5, Lb 7:5, Ws 7:6, Lb 7:7, Ws 7:8, Rb 9:3, Rb 9:3, Eof 9:3]", tz.allTokens().toString());
    assertEquals(new Span(file, 7, 5, 9, 3), tz.span());
  }
  @Test void theSameTextWithoutALayoutKeepsItsOwnPositions(){
    var tz= new Tz().tokenKinds(List.of(K.Lb, K.Rb, K.Ws), K.Sof, K.Eof).input(file, "{ {\n}}").setErrFactory(new Ef()).tokenize();
    assertEquals("[Sof 1:1, Lb 1:1, Ws 1:2, Lb 1:3, Ws 1:4, Rb 2:1, Rb 2:2, Eof 2:3]", tz.allTokens().toString());
    assertEquals(new Span(file, 1, 1, 2, 3), tz.span());
  }
  @Test void unrecognizedTextIsReportedThroughTheLayout(){
    var e= assertThrows(Ex.class, () -> tokenizer("{ x\n}").tokenize());
    assertEquals("unrecognized", e.getMessage());
    assertEquals(new Span(file, 7, 7, 7, 7), e.at);
  }
  @Test void anIllegalCharacterIsReportedThroughTheLayout(){
    var e= assertThrows(Ex.class, () -> tokenizer("{ {\n}x").whiteList("{} \n"));
    assertEquals("illegalChar", e.getMessage());
    assertEquals(new Span(file, 9, 3, 9, 3), e.at);
  }
}
