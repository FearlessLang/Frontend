package metaParser;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Optional;
//TODO: checkGPT
public final class TreeDiagnostics<
    T extends Token<T,TK>,
    TK extends TokenKind,
    E extends RuntimeException & HasFrames<E>,
    Tokenizer extends MetaTokenizer<T,TK,E,Tokenizer,Parser,Err>,
    Parser extends MetaParser<T,TK,E,Tokenizer,Parser,Err>,
    Err extends ErrFactory<T,TK,E,Tokenizer,Parser,Err>
>{
  private final Tokenizer tz;
  private final TokenTreeSpec<T,TK> spec;
  // index helpers over the full token stream
  private final List<T> stream;
  private IdentityHashMap<T,Integer> indexByTok;

  public TreeDiagnostics(TokenTreeSpec<T,TK> spec, Tokenizer tz){
    this.tz = tz;
    this.spec = spec;
    this.stream = tz.allTokens();
  }

  // ==== public entry points ====================================================

  E onBadBarrier(T open, T barrier){
    // prefer specific hints; if none, report MissingCloser at barrier
    if (tryEatenCloserBetween(open, barrier)){ return eatenCloserBetween(open, barrier); }
    if (tryRunOfClosersBefore(open, barrier)){ return runOfClosersBefore(open,barrier); }

    return tz.errFactory().groupHalt(
      open, barrier, expectedClosersFor(open.kind()),
      ErrFactory.LikelyCause.MissingCloser, tz.self());
  }
  E eatenCloserBetween(T open, T stop){ throw new Error("Todo"); }
  E eatenOpenerBetween(T open, T stop){ throw new Error("Todo"); }
  E runOfClosersBefore(T open, T stop){ throw new Error("Todo"); }
  E runOfOpenersBefore(T open, T stop){ throw new Error("Todo"); }

  public E onBadCloser(T open, T badCloser){
    if (tryEatenCloserBetween(open, badCloser)){ return eatenCloserBetween(open, badCloser); }
    if (tryEatenOpenerBetween(open, badCloser)){ return eatenOpenerBetween(open, badCloser); }
    if (tryRunOfClosersBefore(open, badCloser)){ return runOfClosersBefore(open,badCloser); }
    if (tryRunOfOpenersBefore(open, badCloser)){ return runOfOpenersBefore(open,badCloser); }

    throw tz.errFactory().groupHalt(
      open, badCloser, expectedClosersFor(open.kind()),
      ErrFactory.LikelyCause.Unknown, tz.self());
  }

  //public void onEOF(T open){..} NO! this is covered by the case where stop is EOF

  /** Hidden expected closer inside a token between open..stop. */
  private boolean tryEatenCloserBetween(T open, T stop){
    var expect = expectedClosersFor(open.kind());
    for (var closerK : expect){
      var eater = spec.closerEaters.get(closerK);
      if (eater == null) continue;
      for (var tok : betweenExclusive(open, stop)){
        Optional<T> frag = eater.apply(tok);
        if (frag.isPresent()){
          throw tz.errFactory().eatenCloserBetween(
            open, stop, expect, frag.get(), tok, tz.self());
        }
      }
    }
    return false;
  }

  /** Hidden opener-for-stop inside a token between open..stop. */
  private boolean tryEatenOpenerBetween(T open, T stop){
    if (!spec.closers.contains(stop.kind())) return false;
    TK needOp = openerForCloser(stop.kind());
    var eater = spec.openerEaters.get(needOp);
    if (eater == null) return false;
    for (var tok : betweenExclusive(open, stop)){
      Optional<T> frag = eater.apply(tok);
      if (frag.isPresent()){
        throw tz.errFactory().eatenOpenerBetween(
          open, stop, expectedClosersFor(open.kind()), frag.get(), tok, tz.self());
      }
    }
    return false;
  }

  /** Contiguous run of expected closers right before stop (pile-of-closers). */
  private boolean tryRunOfClosersBefore(T open, T stop){
    var run = findRunOfClosersBefore(open, stop);
    if (!run.isEmpty()){
      throw tz.errFactory().runOfClosersBefore(
        open, stop, expectedClosersFor(open.kind()), run, tz.self());
    }
    return false;
  }

  /** Contiguous run of the opener that matches stop’s closer (pile-of-openers). */
  private boolean tryRunOfOpenersBefore(T open, T stop){
    if (!spec.closers.contains(stop.kind())) return false;
    var run = findRunOfOpenersBefore(stop);
    if (!run.isEmpty()){
      throw tz.errFactory().runOfOpenersBefore(
        open, stop, expectedClosersFor(open.kind()), run, tz.self());
    }
    return false;
  }

  // ==== low-level scans (seed heuristics; extend later) ========================

  private List<T> findRunOfClosersBefore(T open, T stop){
    var want = expectedClosersFor(open.kind());
    var out = new ArrayList<T>();
    int j = pos(stop) - 1;
    while (j >= 0){
      var t = stream.get(j);
      if (want.contains(t.kind())){ out.addFirst(t); j--; continue; }
      break; // TODO: tolerate minimal trivia here
    }
    // heuristic: require 2+ to call it a "pile"
    return out.size() >= 2 ? List.copyOf(out) : List.of();
  }

  private List<T> findRunOfOpenersBefore(T stop){
    TK needOp = openerForCloser(stop.kind());
    var out = new ArrayList<T>();
    int j = pos(stop) - 1;
    while (j >= 0){
      var t = stream.get(j);
      if (t.is(needOp)){ out.addFirst(t); j--; continue; }
      break; // TODO: tolerate minimal trivia here
    }
    return out.size() >= 2 ? List.copyOf(out) : List.of();
  }

  // ==== tiny helpers ===========================================================

  private List<TK> expectedClosersFor(TK opener){
    var m = spec.openClose.get(opener);
    assert m != null : "unknown opener " + opener;
    return m.keySet().stream().sorted((a,b)->Integer.compare(a.priority(), b.priority())).toList();
  }

  private TK openerForCloser(TK closer){
    TK found = null;
    for (var e : spec.openClose.entrySet()){
      if (e.getValue().containsKey(closer)){
        assert found == null : "ambiguous closer " + closer;
        found = e.getKey();
      }
    }
    assert found != null : "no opener for closer " + closer;
    return found;
  }

  private int pos(T t){
    if (indexByTok == null){
      indexByTok = new IdentityHashMap<>();
      for (int i = 0; i < stream.size(); i++) indexByTok.put(stream.get(i), i);
    }
    Integer p = indexByTok.get(t);
    assert p != null : "token not in stream";
    return p;
  }

  private List<T> betweenExclusive(T a, T b){
    int i = pos(a), j = pos(b);
    assert i < j : "order mismatch";
    return stream.subList(i + 1, j);
  }
}