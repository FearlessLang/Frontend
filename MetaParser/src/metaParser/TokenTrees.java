package metaParser;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;

//package private so we do not need to make private fields or to otherwise protect from the library user
record TokenTrees<
    T extends Token<T,TK>,
    TK extends TokenKind,
    E extends RuntimeException & HasFrames<E>,
    Tokenizer extends MetaTokenizer<T,TK,E,Tokenizer,Parser,Err>,
    Parser extends MetaParser<T,TK,E,Tokenizer,Parser,Err>,
    Err extends ErrFactory<T,TK,E,Tokenizer,Parser,Err>
  >(
    TokenTreeSpec<T,TK> spec,
    Tokenizer tokenizer){
  TK closesMe(TK open,TK close){//null for not valid closing
    return spec.openClose.getOrDefault(open,Map.of()).get(close);
  }
  List<TK> closers(TK open){//null for not valid opener
    assert spec.openClose.containsKey(open):
      "";
    return spec.openClose.get(open).keySet()
      .stream().sorted(Comparator.comparing(TK::priority)).toList();
  }
  T of(List<T> ts){
    var it= ts.listIterator();
    var first=it.next();
    return new Builder<>(this,new ArrayList<>(List.of(first)),it).build(first);
  }
  Span spanOf(T first, T last){
    return Token.makeSpan(tokenizer.fileName(), first, last);
  }
}