package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.net.URI;
import java.util.List;
import org.junit.jupiter.api.Test;

import metaParser.ErrFactory;
import metaParser.Frame;
import metaParser.HasFrames;
import metaParser.MetaParser;
import metaParser.MetaTokenizer;
import metaParser.Span;
import metaParser.Token;
import metaParser.TokenKind;
import metaParser.TokenMatch;
import utils.Bug;

public class EdgeSkipSpanTest{
  enum K implements TokenKind{
    X, Y, Ws;
    public TokenMatch matcher(){ return TokenMatch.fromRegex(name()); }
    public int priority(){ return 0; }
  }
  record Tk(K kind, String content, int line, int column, List<Tk> tokens) implements Token<Tk,K>{}
  @SuppressWarnings("serial")
  static class Ex extends RuntimeException implements HasFrames<Ex>{
    public Ex addFrame(Frame f){ return this; }
  }
  interface Ef extends ErrFactory<Tk,K,Ex,Tz,P,Ef>{}
  static class Tz extends MetaTokenizer<Tk,K,Ex,Tz,P,Ef>{
    public Tz self(){ return this; }
    public Tk make(K kind, String text, int line, int col, List<Tk> tokens){ return new Tk(kind,text,line,col,tokens); }
  }
  static class P extends MetaParser<Tk,K,Ex,Tz,P,Ef>{
    P(Span s, List<Tk> ts){ super(s,ts); }
    public P self(){ return this; }
    public boolean skip(Tk t){ return t.is(K.Ws); }
    public P make(Span s, List<Tk> ts){ return new P(s,ts); }
    public Ef errFactory(){ throw Bug.unreachable(); }
  }
  static final URI f= URI.create("mem:/t");
  static Tk leaf(K k, String text, int col){ return new Tk(k,text,1,col,List.of()); }

  @Test void remainingSpanStartingWithWhiteSpace(){
    var p= new P(new Span(f,1,1,1,3), List.of(leaf(K.X,"x",1), leaf(K.Ws," ",2), leaf(K.Y,"y",3)));
    p.expect("x", K.X);
    assertEquals(new Span(f,1,3,1,3), p.remainingSpan());
  }
  @Test void spanAroundStartingWithWhiteSpace(){
    var p= new P(new Span(f,1,1,1,4), List.of(leaf(K.Ws," ",1), leaf(K.X,"abc",2)));
    assertEquals(new Span(f,1,2,1,4), p.spanAround(0,1));
  }
}
