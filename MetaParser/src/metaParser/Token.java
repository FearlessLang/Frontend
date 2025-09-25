package metaParser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;
import java.util.ListIterator;
import java.util.Map;

public interface Token<T extends Token<T,TK>, TK extends TokenKind> {
  TK kind();
  String content();
  int line();
  int column();
  List<T> tokens();
  @SuppressWarnings("unchecked")
  default boolean is(TK...kinds){
    assert kinds.length > 0;
    return Stream.of(kinds).anyMatch(this::is);
  }
  default boolean is(TK k){ return kind().equals(k); }
}
//all below properly package private
record TokenTrees<T extends Token<T,TK>, TK extends TokenKind>(
    Set<TK> closers,
    Map<TK,Map<TK,TK>> openClose,
    MetaTokenizer<T,TK> tokenizer){
  TK closesMe(TK open,TK close){//null for not valid closing
    return openClose.getOrDefault(open,Map.of()).get(close);
  }
  Set<TK> closers(TK open){//null for not valid opener
    assert openClose.containsKey(open):
      "";
    return openClose.get(open).keySet();
  }
  T of(List<T> ts){
    var it= ts.listIterator();
    var first=it.next();
    return new Builder<T,TK>(this,new ArrayList<>(List.of(first)),it).build(first);
  }
}
record Builder<T extends Token<T,TK>, TK extends TokenKind>
  (TokenTrees<T,TK> ctx, ArrayList<T> output, ListIterator<T> i){
  Token<T,TK> myOpen(){ return output.getFirst(); }
  T build(T open){
    while (i.hasNext()){
      var current= i.next();
      if (!commit(open,current)){ continue; }
      TK groupKind= ctx.closesMe(open.kind(),current.kind());
      return ctx.tokenizer().make(groupKind,"",
        myOpen().line(),
        myOpen().column(),
        Collections.unmodifiableList(output));
    }
    var expected = ctx.closers(open.kind());
    throw ctx.tokenizer().unclosedError(open,expected);
  }
  boolean commit(T open,T t){
    TK end= ctx.closesMe(open.kind(),t.kind());
    if (end != null){ return output.add(t); }//the group must contain the opener and the closer
    //so we can have tokens like "{ a, b, c }" but also "(2,4]", where the open/close token are relevant
    boolean opener= ctx.openClose().keySet().contains(t.kind());
    if (opener){
      T tree= new Builder<T,TK>(ctx,new ArrayList<>(List.of(t)),i).build(t);
      return !output.add(tree);
    }
    boolean regular= !ctx.closers().contains(t.kind());
    if(regular){ return !output.add(t); }
    throw ctx.tokenizer().unopenedCloserError(open,t);
  }
}