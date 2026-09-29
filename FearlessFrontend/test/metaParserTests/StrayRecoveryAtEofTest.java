package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.net.URI;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.jupiter.api.Test;

import metaParser.ErrFactory;
import metaParser.ErrFactory.LikelyCause;
import metaParser.Frame;
import metaParser.HasFrames;
import metaParser.MetaParser;
import metaParser.MetaTokenizer;
import metaParser.Span;
import metaParser.Token;
import metaParser.TokenKind;
import metaParser.TokenMatch;
import metaParser.TokenTreeSpec;

public class StrayRecoveryAtEofTest{
  enum K implements TokenKind{
    Sof("(?!)"), Eof("(?!)"), Lb("\\{"), Rb("\\}"), Lp("\\("), Rp("\\)"), File("(?!)"), Braces("(?!)"), Parens("(?!)");
    final TokenMatch m;
    K(String r){ m= TokenMatch.fromRegex(r); }
    public TokenMatch matcher(){ return m; }
    public int priority(){ return 0; }
  }
  record Tok(K kind, String content, int line, int column, List<Tok> tokens) implements Token<Tok,K>{}
  @SuppressWarnings("serial")
  static class Ex extends RuntimeException implements HasFrames<Ex>{
    final String name; final LikelyCause likely; final ArrayList<Frame> frames= new ArrayList<>();
    Ex(String name, LikelyCause likely){ super(name+" "+likely); this.name= name; this.likely= likely; }
    public Ex addFrame(Frame f){ frames.add(f); return this; }
  }
  static class Tz extends MetaTokenizer<Tok,K,Ex,Tz,Ps,Ef>{
    public Tz self(){ return this; }
    public Tok make(K kind, String text, int line, int col, List<Tok> tokens){ return new Tok(kind,text,line,col,tokens); }
  }
  static class Ps extends MetaParser<Tok,K,Ex,Tz,Ps,Ef>{
    Ps(Span s, List<Tok> ts){ super(s,ts); }
    public Ps self(){ return this; }
    public boolean skip(Tok t){ return t.is(K.Sof,K.Eof); }
    public Ps make(Span s, List<Tok> ts){ return new Ps(s,ts); }
    public Ef errFactory(){ return new Ef(); }
  }
  static class Ef implements ErrFactory<Tok,K,Ex,Tz,Ps,Ef>{
    public Ex illegalCharAt(Span at, int cp, Tz tz){ return new Ex("illegalChar",null); }
    public Ex unrecognizedTextAt(Span at, String what, Tz tz){ return new Ex("unrecognized",null); }
    public Ex groupHalt(Tok open, Tok stop, Collection<K> closers, LikelyCause likely, Tz tz){ return new Ex("groupHalt",likely); }
    public Ex eatenCloserBetween(Tok open, Tok stop, Collection<K> closers, Tok frag, Tok container, Tz tz){ return new Ex("eatenCloser",null); }
    public Ex eatenOpenerBetween(Tok open, Tok stop, Collection<K> closers, Tok frag, Tok container, Tz tz){ return new Ex("eatenOpener",null); }
    public Ex missing(Span at, String what, List<K> expected, Ps p){ return new Ex("missing",null); }
    public Ex missingButFound(Span at, String what, Tok found, Collection<K> expected, Ps p){ return new Ex("missingButFound",null); }
    public Ex extraContent(Span from, String what, Collection<K> expected, Ps p){ return new Ex("extraContent",null); }
    public Ex probeStalledIn(String label, Span at, int s, int e, Ps p){ return new Ex("probeStalled",null); }
    public Ex badProbeDropIn(String label, Span at, int s, int e, int drop, Ps p){ return new Ex("badProbeDrop",null); }
  }
  static Ex treeError(String src){
    var spec= new TokenTreeSpec<Tok,K>()
      .addOpenClose(K.Sof,K.Eof,K.File)
      .addOpenClose(K.Lb,K.Rb,K.Braces)
      .addOpenClose(K.Lp,K.Rp,K.Parens);
    var tz= new Tz()
      .tokenKinds(List.of(K.Lb,K.Rb,K.Lp,K.Rp),K.Sof,K.Eof)
      .input(URI.create("fear:/a.fear"),src)
      .setErrFactory(new Ef())
      .tokenize();
    return assertThrows(Ex.class,()->tz.buildTokenTree(spec));
  }
  @Test void unclosedParenInsideBracesIsStrayOpener(){
    var e= treeError("{(}");
    assertEquals("groupHalt",e.name);
    assertEquals(LikelyCause.StrayOpener,e.likely);
  }
  @Test void unclosedBraceInsideParensIsStrayOpener(){
    var e= treeError("({)");
    assertEquals("groupHalt",e.name);
    assertEquals(LikelyCause.StrayOpener,e.likely);
  }
}
