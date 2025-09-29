package metaParser;

import java.net.URI;
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
  static Span makeSpan(URI fileName, Token<?,?> first, Token<?,?> last){
    int l = last.line();
    int c = last.column();
    for (int i = 0; i < last.content().length();) {
      int cp= last.content().codePointAt(i);
      i += Character.charCount(cp);
      if (cp == '\n'){ l += 1; c = 1; } else { c += 1; }
    }
    return new Span(fileName, first.line(),first.column(),l,c-1);
  }
}
//all below properly package private
record TokenTrees<T extends Token<T,TK>, TK extends TokenKind,E extends RuntimeException & HasFrames<?>>(
    Set<TK> closers,
    Map<TK,Map<TK,TK>> openClose,
    MetaTokenizer<T,TK,E> tokenizer){
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
    return new Builder<T,TK,E>(this,new ArrayList<>(List.of(first)),it).build(first);
  }
  Span spanOf(T first, T last){
    return Token.makeSpan(tokenizer.fileName(), first, last);
  }
}
record Builder<T extends Token<T,TK>, TK extends TokenKind,E extends RuntimeException & HasFrames<?>>
  (TokenTrees<T,TK,E> ctx, ArrayList<T> output, ListIterator<T> i){
  Token<T,TK> myOpen(){ return output.getFirst(); }
  T build(T open){
    T current= open;
    while (i.hasNext()){
      current= i.next();
      if (!commit(open,current)){ continue; }
      TK groupKind= ctx.closesMe(open.kind(),current.kind());
      return ctx.tokenizer().make(groupKind,"",
        myOpen().line(),
        myOpen().column(),
        Collections.unmodifiableList(output));
    }
    String openStr= open.kind().toString();//TODO: should we enrich the generics to pass the use Token, they may have methods for pretty printing etc
    throw ctx.tokenizer().errFactory().unclosedIn(openStr, ctx.spanOf(open,current), ctx.closers(open.kind()));
  }
  boolean commit(T open,T t){
    TK end= ctx.closesMe(open.kind(),t.kind());
    if (end != null){ return output.add(t); }//the group must contain the opener and the closer
    //so we can have tokens like "{ a, b, c }" but also "(2,4]", where the open/close token are relevant
    boolean opener= ctx.openClose().keySet().contains(t.kind());
    if (opener){
      T tree= new Builder<T,TK,E>(ctx,new ArrayList<>(List.of(t)),i).build(t);
      return !output.add(tree);
    }
    boolean regular= !ctx.closers().contains(t.kind());
    if(regular){ return !output.add(t); }
    String groupLabel= t.kind().toString();
    throw ctx.tokenizer().errFactory().unopenedIn(groupLabel, ctx.spanOf(open,t));
  }
}