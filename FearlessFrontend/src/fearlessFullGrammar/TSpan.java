package fearlessFullGrammar;

import utils.Pos;
import metaParser.Span;
import offensiveUtils.EqTransparent;
import offensiveUtils.NeverAsKey;

/** Never as Map/Set key (nondiscriminating equals/hashCode). Build-time checker rejects it. */
@NeverAsKey
public class TSpan extends EqTransparent<Span>{
  public TSpan(Span inner){ super(inner); }
  public Pos pos(){ return new Pos(inner.fileName(),inner.startLine(),inner.startCol());}
  public static TSpan fromPos(Pos pos){ return fromPos(pos,1); }
  public static TSpan fromPos(Pos pos, int size){ return new TSpan(new Span(pos.fileName(),pos.line(),pos.column(),pos.line(),pos.column()+size)); }
  public static TSpan merge(TSpan a, TSpan b){
    return new TSpan(new Span(a.inner.fileName(),a.inner.startLine(),a.inner.startCol(),b.inner.endLine(),b.inner.endCol()));
  }
}
