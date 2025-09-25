package metaParser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

public abstract class MetaTokenizer<T extends Token<T,TK>, TK extends TokenKind>{
  private final List<TK> kinds;
  private final TK sof;
  private final TK eof;
  private String input;
  private int pos;
  private int line;
  private int col;
  //the true tokens, ignore any special marker
  public MetaTokenizer(List<TK> tks, TK sof, TK eof){
    this.sof= sof;
    this.eof= eof;
    this.kinds= tks; 
    }
  public List<T> tokenize(String i){
    input= i; pos=0; line=1; col=1;
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
  private final RuntimeException error(){ return unrecognizedTokenError(line,col); }  
  public RuntimeException unrecognizedTokenError(int line,int col){
    return new RuntimeException("Unrecognized token at "+line+":"+col+".");
  }
  public RuntimeException unclosedError(T open, Set<TK> validClosers){
    return new RuntimeException("Unclosed group starting at "+open.line()+":"+open.column()+
      " ("+open.kind()+"); expected one of: "+validClosers+".");
  }
  public RuntimeException unopenedCloserError(T open,T closer){
    return new RuntimeException("Unopened closer "+closer.kind()+" at "+closer.line()+":"+closer.column()+
      " while parsing group opened by "+open.kind()+" at "+open.line()+":"+open.column()+".");
  }  
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
  public List<T> tokenize(String i,
      Map<TK,Map<TK,TK>> openClose){
    var ts= tokenize(i);
    var closers= openClose.values().stream()
      .flatMap(s->s.keySet().stream())
      .collect(Collectors.toSet());
    return new TokenTrees<T,TK>(closers,openClose,this).of(ts).tokens();
  }
}