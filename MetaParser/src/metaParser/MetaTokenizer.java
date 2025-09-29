package metaParser;

import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public abstract class MetaTokenizer<T extends Token<T,TK>, TK extends TokenKind,E extends RuntimeException & HasFrames<?>>{
  private final List<TK> kinds;
  private final TK sof;
  private final TK eof;
  private final URI fileName;
  private final String input;
  private int pos;
  private int line;
  private int col;
  //the true tokens, ignore any special marker
  public MetaTokenizer(URI fileName, String input, List<TK> tks, TK sof, TK eof){
    this.sof= sof;
    this.eof= eof;
    this.kinds= tks;
    this.fileName= fileName;
    this.input= input;
  }
  private final RuntimeException error(){ 
    return errFactory().unrecognizedTextAt(new Span(fileName,line,col,line,col),"");
  }  

  public List<T> tokenize(int _line, int _col){
    pos=0; this.line=_line; this.col=_col;
    var out= new ArrayList<T>();
    out.add(make(sof,"", line, col,List.of()));
    while (pos < input.length()){
      var best = findNext().orElseThrow(this::error);
      if(!best.kind().hidden()){ out.add(best); }
      advance(best.content());
    }
    out.add(make(eof,"", line, col,List.of()));
    return Collections.unmodifiableList(out);
  }
  public abstract ErrFactory<E,TK> errFactory();
  public abstract T make(TK kind, String text, int line, int col, List<T> tokens);
  private Optional<T> current(TK kind){
    return kind
      .matcher().apply(input, pos)
      .map(text -> make(kind, text, line, col,List.of()));
  }
  private Optional<T> findNext(){
    return kinds.stream()
      .flatMap(k -> current(k).stream())
      .max(Comparator
        .<T>comparingInt(t -> t.content().length())
        .thenComparingInt(t -> -t.kind().priority()));
  }
  private void advanceSingle(int cp){
    if (cp == '\n'){ line++; col = 1; } else { col++; }
  }
  private void advance(String matched){
    matched.codePoints().forEach(this::advanceSingle);
    pos += matched.length();
  }
  /// 1,1 is good default for line/col
  public Tokens<T,TK> tokenize(Map<TK,Map<TK,TK>> openClose,int line, int col){
    var ts= tokenize(line,col);
    var closers= openClose.values().stream()
      .flatMap(s->s.keySet().stream())
      .collect(Collectors.toSet());
    var tree= new TokenTrees<T,TK,E>(closers,openClose,this).of(ts).tokens();
    assert ts.size() > 2;
    var first= ts.get(1);//ts.getFirst() is SOF
    var last= ts.get(ts.size()-2);//ts.getLast() is EOF
    Span base= metaParser.Token.makeSpan(fileName,first,last);
    return new Tokens<T,TK>(base,ts,tree);
  }
  public URI fileName(){ return fileName; }
}