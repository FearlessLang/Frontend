package metaParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.stream.IntStream;

public abstract class MetaParser<
    P extends MetaParser<P,T,TK>,    
    T extends Token<T,TK>,
    TK extends TokenKind>{
  private final List<T> ts;
  private int index= 0;
  private int limit;
  public abstract P self();
  public abstract P make(List<T> tokens);
  public MetaParser(List<T> ts){ this.ts= ts; this.limit= ts.size(); }
  public <R> R parseAll(Rule<P,T,TK,R> r){
    var res= r.parse(this.self());
    if(index != limit){ throw unconsumedTokensError(); }
    return res;
  }
  public boolean end(){ return limit == index; }
  public int remaining(){ return limit - index; }
  public int index(){ return index; }
  public int limit(){ return limit; }
  public void setIndex(int index){ this.index = index; }

  public Optional<T> peek(){ return peek(0); }
  public Optional<T> peekAbs(int index){
    if (index < this.index || index >= limit){ return Optional.empty(); }
    return Optional.of(ts.get(index));
  }
  private T currentT(){ return index<ts.size()? ts.get(index) : ts.get(index-1); }
  public int currentLine(){ return currentT().line(); }
  public int currentCol(){ return  currentT().column(); }
  public Optional<T> peek(int la){ return peekAbs(index + la); }
  public Optional<T> peekLast(){ return peekLast(0); }
  public Optional<T> peekLast(int la){ return peekAbs((limit-la)-1); }
  
  @SafeVarargs
  public final boolean peek(TK... kinds){
    assert kinds.length > 0;
    var t= peek();
    return t.map(tt->tt.is(kinds)).orElse(false);
  }
  public final T expectAny(String what){
    var t= peek();
    if (t.isEmpty()){ throw unexpectedEndOfGroupError(what,ts.get(limit-1)); }
    var tt= t.get();
    index++;
    return tt;
  }
  @SafeVarargs
  public final T expect(String what,TK... kinds){
    var t= peek();
    if (t.isEmpty()){ throw unexpectedEndOfGroupError(what,ts.get(limit-1)); }
    var tt= t.get();
    var allowed= tt.is(kinds);
    if (!allowed){ throw unexpectedTokenError(what,tt,List.of(kinds)); }
    index++;
    return tt;
  }
  @SafeVarargs
  public final T expectLast(String what, TK... kinds){
    var last= peekLast();
    if (last.isEmpty()){ throw unexpectedEndOfGroupError(what,ts.get(limit-1)); }
    var t= last.get();
    var allowed= t.is(kinds);
    if (!allowed){ throw unexpectedTokenError(what,t,List.of(kinds)); }
    limit--;
    return t;
  }

  public RuntimeException unconsumedTokensError(){
    var next = ts.get(index);
    return new RuntimeException("Expected end of input, found "+PrettyToken.show(next)+" (index="+index+"/"+limit+").");
  }
  public RuntimeException unexpectedEndOfGroupError(String what,T last){
    return new RuntimeException("Searching for "+what+": Unexpected end of group after "+PrettyToken.show(last)+".");
  }
  //TODO: why is this dead code?
  /*public RuntimeException unexpectedStartOfGroupError(String what,T first){
    return new RuntimeException("Searching for "+what+": Unexpected start of group before "+PrettyToken.show(first)+".");
  }*/
  public RuntimeException unexpectedTokenError(String what, T got, List<TK> expected){
    return new RuntimeException("Searching for "+what+": Unexpected "+PrettyToken.show(got)+"; expected: "+expected+".");
  }
  public boolean peekIf(Predicate<T> p){
    return peek().map(p::test).orElse(false);
  }
  @SafeVarargs
  public final boolean peekOrder(Predicate<T>... ps){
    return IntStream.range(0, ps.length)
      .mapToObj(i->peek(i).filter(t->ps[i].test(t)))
      .allMatch(Optional::isPresent);
  }
  public <R> R back(R v){
    if (index == 0) { throw new IllegalStateException("Can not go back since already at start"); }
    index--;
    return v;
    }
  public <R> R fwd(R v){
    if (index == limit){ throw new IllegalStateException("Can not go fwd since already at end"); }
    index++;
    return v;
  }
  public boolean fwdIf(boolean v){
    if(v){ return fwd(true); }
    return false;
  } 
  public <R> R trim(R v){
    if (index == limit){ throw new IllegalStateException("Can not go trim since already empty"); }
    limit--;
    return v;
  }
  public boolean trimIf(boolean v){
    if(v){ return trim(true); }
    return false;
  }
  
  //ParseSplitters
  public <R> R parseGroup(Rule<P,T,TK,R> r){
    var tsIn= ts.get(index).tokens();
    if(tsIn.isEmpty()){ throw new IllegalStateException("Expected a grouped token (with children), got "+PrettyToken.show(ts.get(index))+"."); }
    var nested= make(tsIn);
    var res= nested.parseAll(r);
    index++;
    return res;
  }
  public <R> R parseRemaining(Rule<P,T,TK,R> r){
    var tsIn= ts.subList(index, limit);
    if(tsIn.isEmpty()){ throw new IllegalStateException("Expected a grouped token (with children), got "+PrettyToken.show(ts.get(index))+"."); }
    var nested= make(tsIn);
    var res= nested.parseAll(r);
    index = limit;
    return res;
  }
  
  ///Must advance p.index() by >= 1; will be called until p.end() holds
  ///Returns the amount of last consumed token to drop as separators
  public interface NextCut<P extends MetaParser<P,T,TK>, T extends Token<T,TK>, TK extends TokenKind>{ int cutAt(P p); }
  public interface Rule<P extends MetaParser<P,T,TK>, T extends Token<T,TK>, TK extends TokenKind, R> { R parse(P p); }
  //public interface RuleArg<A,P extends MetaParser<P,T,TK>, T extends Token<T,TK>, TK extends TokenKind, R> { R parse(A a, P p); }
  
  public <R> List<R> splitBy(NextCut<P,T,TK> probe, Rule<P,T,TK,R> elem){
    var parts= _splitBy(probe);
    var res= parts.stream().map(this::make).map(p -> p.parseAll(elem)).toList();
    index = limit;//only update outer parser if no failures
    return res;
  }
  private final List<List<T>> _splitBy(NextCut<P,T,TK> probe){
    var slice= ts.subList(index, limit);
    P splitterParser= make(slice);
    var parts= new ArrayList<List<T>>();
    while (!splitterParser.end()){
      int start= splitterParser.index();
      int drop= probe.cutAt(splitterParser);
      if (drop < 0){ throw new IllegalStateException("NextCut.cutAt retuned negative " + drop); }
      int end= splitterParser.index();
      if (start >= end){ throw new IllegalStateException("split probe did not advance (start="+start+", end="+end+")"); }
      parts.add(List.copyOf(slice.subList(start, end-drop)));
    }
    return parts;
  }
  public <R> List<R> parseGroupSep(String what,Rule<P,T,TK,R> r,TK open, TK close, NextCut<P,T,TK> probe){
    return parseGroup(p->{
      p.expect(what,open);
      p.expectLast(what,close);
      return p.splitBy(probe,r);
    });
  }

  ///Suitable to divide two non empty lists of tokens, especially if
  ///the division can not be easily located by looking at a few tokens forward.
  ///Parses a non empty list of tokens from the start of this parser.
  ///Must be a proper division.
  ///The probe accepting all the token signals no prefix. 
  public final <R> Optional<R> parseUpTo(NextCut<P,T,TK> probe, Rule<P,T,TK,R> first){
    var slice= ts.subList(index, limit);
    P splitterParser= make(slice);
    int drop= probe.cutAt(splitterParser);
    if (drop < 0){ throw new IllegalStateException("NextCut.cutAt retuned negative " + drop); }
    int end= splitterParser.index();
    if (end == 0){ throw new IllegalStateException("split probe did not advance (start="+0+", end="+end+")"); }
    if(splitterParser.end()){ return Optional.empty(); }//split not found
    P firstParser= make(List.copyOf(slice.subList(0, end-drop)));
    var res= firstParser.parseAll(first);
    this.index+= end;//mark the tokens as eaten
    return Optional.of(res);
  }
  public enum SplitMode{Skipped,Left,Right}
  public int splitOn(SplitMode split, TK k){
    while(!end()){
      var t= expectAny("");
      if (!t.is(k)){ continue; }
      return switch(split){
      case Skipped-> 1;
      case Left-> 0;
      case Right-> back(0);
      };
    }
    return 0;
  }
  @Override
  public String toString(){
    StringBuilder sb = new StringBuilder(128);
    // [0..index)
    appendRange(sb, 0, index);
    sb.append('(').append(index).append(')');
    // [index..limit)
    appendRange(sb, index, limit);
    sb.append('(').append(limit).append(')');
    // [limit..ts.size())
    appendRange(sb, limit, ts.size());
    return sb.toString();
  }

  private void appendRange(StringBuilder sb, int from, int to){
    sb.append('[');
    for(int i=from;i<to;i++){
      if(i>from) sb.append(", ");
      sb.append(PrettyToken.show(ts.get(i)));
    }
    sb.append(']');
  }
  private Optional<T> firstLeaf(List<T> ts, Predicate<T> skip){
    for (var t:ts){
      Optional<T> leaf= firstLeaf(t,skip);
      if (leaf.isPresent()){ return leaf; }
    }
    return Optional.empty();
  }
  private Optional<T> firstLeaf(T t, Predicate<T> skip){
    if (skip.test(t)){ return Optional.empty(); } 
    if (t.tokens().isEmpty()){ return Optional.of(t); }
    return firstLeaf(t.tokens(),skip);
  }
  private Optional<T> lastLeaf(List<T> ts, Predicate<T> skip){
    for (var t:ts.reversed()){
      Optional<T> leaf= lastLeaf(t,skip);
      if (leaf.isPresent()){ return leaf; }
    }
    return Optional.empty();
  }
  private Optional<T> lastLeaf(T t, Predicate<T> skip){
    if (skip.test(t)){ return Optional.empty(); } 
    if (t.tokens().isEmpty()){ return Optional.of(t); }
    return lastLeaf(t.tokens(),skip);
  }
  public Span span(Predicate<T> skip){
    T first= firstLeaf(ts,skip).orElseThrow(()-> new IllegalStateException("Invalid span for "+this));
    T last=  lastLeaf(ts,skip).orElseThrow(()-> new IllegalStateException("Invalid span for "+this));
    return span(first,last);
  }
  public Span span(T t, Predicate<T> skip){
    System.out.println(this);
    T first= firstLeaf(t,skip).orElseThrow(()-> new IllegalStateException("Invalid span for "+this));
    T last=  lastLeaf(t,skip).orElseThrow(()-> new IllegalStateException("Invalid span for "+this));
    return span(first,last);
  }
  private Span span(T first, T last){
    int l = last.line();
    int c = last.column();
    for (int i = 0; i < last.content().length();) {
      int cp= last.content().codePointAt(i);
      i += Character.charCount(cp);
      if (cp == '\n'){ l += 1; c = 1; } else { c += 1; }
    }
    return new Span(first.line(),first.column(),l,c-1);
  }
  public record Span(int startLine, int startCol, int endLine, int endCol){}
}