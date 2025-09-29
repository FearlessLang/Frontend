package metaParser;

import java.util.Collection;
import java.util.List;

public interface ErrFactory<E extends RuntimeException & HasFrames<?>, TK extends TokenKind>{

  E illegalCharAt(Span at, String what);
  E unrecognizedTextAt(Span at, String what);

  E unclosedIn(String what, Span openedAt, Collection<TK> expectedClosers);
  E unopenedIn(String what, Span closerAt);

  ///empty expectedLabels means no info
  E missing(Span at, String what, List<TK> expectedLabels);
  E missingButFound(Span at, String what, String found, Collection<TK> expectedLabels);
  E extraContent(Span from);

  E probeStalledIn(String groupLabel, Span at, int startIdx, int endIdx);
  E badProbeDropIn(String groupLabel, Span at, int startIdx, int endIdx, int drop);
}