package message;

import java.io.Serializable;
import java.net.URI;
import java.util.Objects;
import static offensiveUtils.Require.*;
import files.Pos;

/** Half-open span [start..end] in source. Start and end are inclusive in line/col intent,
 * but formatting will use them as caret anchors. Equality/hash ignore Pos.equals and use real fields.*/
public record Span(Pos start, Pos end) implements Serializable {
  private static final long serialVersionUID = 1L;
  public static Span of(Pos a, Pos b){ return new Span(a, b); }
  public Span{
    assert start.fileName().equals(end.fileName());
    assert nonNull(start,end);
  }
  public Span(URI fileName, metaParser.MetaParser.Span span){ this(
    new Pos(fileName,span.startLine(),span.startCol()),
    new Pos(fileName,span.endLine(),span.endCol()));
  }
  public URI fileName(){ return start.fileName(); }

  public boolean isSingleLine(){ return  start.line() == end.line(); }

  @Override public boolean equals(Object o){
    if(this == o){ return true; }
    if(!(o instanceof Span s)){ return false; }
    return eqPos(this.start, s.start) && eqPos(this.end, s.end);
  }
  @Override public int hashCode(){
    return Objects.hash(hashPos(start), hashPos(end));
  }
  @Override public String toString(){
    return start.fileName()+"["+posToString(start)+".."+posToString(end)+"]";
  }
  private static boolean eqPos(Pos a, Pos b){
    return a.line() == b.line() && a.column() == b.column();
  }
  private static int hashPos(Pos p){
    return Objects.hash(p.line(), p.column());
  }
  private static String posToString(Pos p){
    return p.line()+":"+p.column();
  }
}