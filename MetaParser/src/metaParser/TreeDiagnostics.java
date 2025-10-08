package metaParser;

import java.util.List;
import java.util.Optional;
import java.util.stream.IntStream;

import metaParser.ErrFactory.LikelyCause;

import static metaParser.ErrFactory.LikelyCause.*;

record TreeDiagnostics<
    T extends Token<T,TK>,
    TK extends TokenKind,
    E extends RuntimeException & HasFrames<E>,
    Tokenizer extends MetaTokenizer<T,TK,E,Tokenizer,Parser,Err>,
    Parser extends MetaParser<T,TK,E,Tokenizer,Parser,Err>,
    Err extends ErrFactory<T,TK,E,Tokenizer,Parser,Err>
  >(TokenTreeSpec<T,TK> spec, Tokenizer tz){

  public E onBadCloser(T open, T badCloser){
    return Optional.<E>empty()
    .or(()->tryEatenCloserBetween(open, badCloser))
    .or(()->tryEatenOpenerBetween(open, badCloser))
    .or(()->tryRunOfClosersBefore(open, badCloser))
    .or(()->tryRunOfOpenersBefore(open, badCloser))
    .or(()->tryRemoveClose(open, badCloser))
    .or(()->tryRemoveOpen(open, badCloser))
    .orElseGet(()->baseError(open,badCloser));
  }
  E onBadBarrier(T open, T barrier){
    return Optional.<E>empty()
      .or(()->tryEatenCloserBetween(open, barrier))
      .or(()->tryRunOfClosersBefore(open, barrier))
      .or(()->tryRemoveClose(open, barrier))
      .or(()->tryRemoveOpen(open, barrier))
      .orElseGet(()->baseError(open, barrier));
  }

  private E baseError(T open, T stop){ return error(open,stop,Unknown); }
  private E error(T open, T stop, LikelyCause l){
    return tz.errFactory().groupHalt(open, stop, closersForOpener(open.kind()),l, tz.self());
  }
  private List<TK> openerForCloser(TK closer){
    return spec.openClose.entrySet().stream()
      .filter(e->e.getValue().containsKey(closer))
      .map(e->e.getKey()).toList();
  }
  private List<TK> closersForOpener(TK opener){
    var m= spec.openClose.get(opener);
    assert m != null : "unknown opener " + opener;
    return m.keySet().stream().sorted(
      (a,b)->Integer.compare(a.priority(), b.priority())).toList();
  }
  private Optional<E> tryEatenBetween(T open, T stop, boolean onOpen){
    var expect= !onOpen?closersForOpener(open.kind()):openerForCloser(stop.kind());
    //var expect= closersForOpener(open.kind());
    for (var e : expect){
      var eater= (onOpen?spec.openerEaters:spec.closerEaters).get(e);
      if (eater == null){ continue; }
      var ts= betweenExclusive(open, stop,tz.allTokens());
      for (var tok : onOpen?ts.reversed():ts){
        Optional<T> frag= eater.apply(tok);
        if (frag.isPresent()){ return Optional.of(onOpen
          ?eaterOpenerBetween(open, stop, expect, frag.get(), tok)
          :eaterCloserBetween(open, stop, expect, frag.get(), tok));
        }
      }
    }
    return Optional.empty();    
  }
  private Optional<E> tryRemoveClose(T open, T stop){ return tryRemove(open,stop,StrayCloser,stop); }
  private Optional<E> tryRemoveOpen(T open, T stop){ return tryRemove(open,stop,StrayOpener,open); }
  @SuppressWarnings("unchecked")
  private Optional<E> tryRemove(T open, T stop, LikelyCause l, T remove){
    if(remove.is(tz.sof(),tz.eof())){ return Optional.empty(); }
    List<T> ts= tz.tokensForTree().stream().filter(t->t!=remove).toList();
    int res1= TokenTreeBulder.ofRecovery(spec,tz, tz.tokensForTree());
    int res2= TokenTreeBulder.ofRecovery(spec,tz, ts);
    var progress= ts.size() == res2 || res2 >= res1 + 5;
    if (!progress){ return Optional.empty(); }
    return Optional.of(error(open,stop,l));    
  }
  private Optional<E> tryEatenCloserBetween(T open, T stop){ return tryEatenBetween(open, stop, false); }
  private Optional<E> tryEatenOpenerBetween(T open, T stop){ return tryEatenBetween(open, stop, true); }

  private Optional<E> tryRunOfClosersBefore(T open, T stop){
    return findRunOfClosersBefore(open, stop)
      .map(run->runOfClosersBefore(open, stop, closersForOpener(open.kind()), run));
  }
  private Optional<E> tryRunOfOpenersBefore(T open, T stop){
    if (!spec.closers.contains(stop.kind())){ return Optional.empty(); }
    return findRunOfOpenersBefore(open, stop)
        .map(run->runOfOpenersBefore(open, stop, closersForOpener(open.kind()), run));
  }
  private long count(List<T> ts, int i, List<TK> want){
    return ts.subList(i, i+6).stream().filter(t->want.contains(t.kind())).count();
  }
  private Optional<List<T>> findRunOfClosersBefore(T open, T stop){
    var ts= betweenExclusive(open, stop,tz.tokensForTree());
    if(ts.size() < 6){ return Optional.empty(); }
    var want= closersForOpener(open.kind());
    return IntStream.range(0, ts.size() - 6).boxed()
      .filter(i->count(ts,i,want) >= 3)
      .findFirst()
      .map(i->ts.subList(i,i+6));
  }
  private Optional<List<T>> findRunOfOpenersBefore(T open, T stop){
    var ts= betweenExclusive(open, stop,tz.tokensForTree()).reversed();
    if(ts.size() < 6){ return Optional.empty(); }
    var want= closersForOpener(open.kind());
    return IntStream.range(0, ts.size() - 6).boxed()
      .filter(i->count(ts,i,want) >= 3)
      .findFirst()
      .map(i->ts.subList(i,i+6));
  }
  private List<T> betweenExclusive(T a, T b, List<T> tokens){
    int start= tokens.indexOf(a);
    int end= tokens.indexOf(b);
    assert start < end : "order mismatch";
    return tokens.subList(start + 1, end);
  }
  private E eaterCloserBetween(T open, T stop, List<TK> expect, T frag, T token){
    return tz.errFactory().eatenCloserBetween(open, stop, expect, frag, token, tz.self());
  }
  private E eaterOpenerBetween(T open, T stop, List<TK> expect, T frag, T token){
    return tz.errFactory().eatenOpenerBetween(open, stop, expect, frag, token, tz.self());
  }
  private E runOfClosersBefore(T open, T stop, List<TK> expect, List<T> run){
    return tz.errFactory().runOfClosersBefore(open, stop, expect, run, tz.self());
  }
  private E runOfOpenersBefore(T open, T stop, List<TK> expect, List<T> run){
    return tz.errFactory().runOfOpenersBefore(open, stop, expect, run, tz.self());
  }
}