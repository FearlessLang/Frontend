package metaParser;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Given a target name and a set of candidate names, produce a small
 * multi-line suggestion block, or empty if nothing worth showing.
 *
 * Output policy (tweakable via constants below):
 *  - If candidates are few (<= MAX_SCOPE_TO_LIST), list them deterministically:
 *      "In scope: a, b, c"
 *  - Compute similarity (normalized Levenshtein) for each candidate.
 *  - If exactly one candidate clears a strong threshold AND is clearly
 *    better than the runner-up (by MARGIN), add:
 *      "did you mean `foo` ?"
 *  - If suggestions are ambiguous or weak, we show only the "In scope" line
 *    (if any) and skip the "did you mean" line to avoid misleading hints.
 */
public final class NameSuggester {

  // ---- Tunables --------------------------------------------------------------

  /** If there are this many or fewer names, show the "In scope:" line. */
  private static final int MAX_SCOPE_TO_LIST = 12;

  /** Strong similarity threshold (normalized 0..1). */
  private static final double STRONG_SIM = 0.78;

  /** Extra bonus for same first letter (helps stabilize top-1). */
  private static final double SAME_FIRST_BONUS = 0.03;

  /** Require top-1 to beat top-2 by at least this margin to avoid ambiguity. */
  private static final double MARGIN = 0.08;

  private NameSuggester() {}

  public static Optional<String> suggest(String name, Collection<String> rawCandidates) {
    if (name == null || name.isEmpty() || rawCandidates == null || rawCandidates.isEmpty()) {
      return Optional.empty();
    }

    // Dedup + deterministic order for display.
    List<String> candidates = rawCandidates.stream()
        .filter(Objects::nonNull)
        .filter(s -> !s.isEmpty())
        .distinct()
        .sorted()
        .collect(Collectors.toList());

    if (candidates.isEmpty()) return Optional.empty();

    StringBuilder out = new StringBuilder();

    // 1) Optional "In scope:" line (kept compact & deterministic).
    if (candidates.size() <= MAX_SCOPE_TO_LIST) {
      out.append("In scope: ").append(candidates.stream().map(Message::displayString).collect(Collectors.joining(", "))).append('\n');
    }

    // 2) Compute similarity scores; pick a confident single suggestion or none.
    Suggestion best = pickBest(name, candidates);

    if (best != null && best.isConfident) {
      out.append("did you mean `").append(best.value).append("` ?").append('\n');
    }

    if (out.length() == 0) return Optional.empty(); // nothing to show
    // Trim trailing newline for cleanliness.
    if (out.charAt(out.length() - 1) == '\n') out.setLength(out.length() - 1);
    return Optional.of(out.toString());
  }

  // ---- Scoring / selection ----------------------------------------------------

  private static Suggestion pickBest(String target, List<String> candidates) {
    String t = target;
    boolean tLower = isAllLower(t);
    boolean tUpper = isAllUpper(t);

    List<Suggestion> scored = new ArrayList<>(candidates.size());
    for (String c : candidates) {
      double base = normalizedLevenshtein(t, c);
      // Encourage same first letter (case-insensitive).
      if (!t.isEmpty() && !c.isEmpty() &&
          Character.toLowerCase(t.charAt(0)) == Character.toLowerCase(c.charAt(0))) {
        base += SAME_FIRST_BONUS;
      }
      // Tiny bias toward similar case shape (all-lower vs all-upper).
      if ((tLower && isAllLower(c)) || (tUpper && isAllUpper(c))) {
        base += 0.01;
      }
      double score = clamp01(base);
      scored.add(new Suggestion(c, score));
    }

    // Rank by score desc, then shorter edit distance proxy (length gap), then lexicographically.
    scored.sort(Comparator
        .comparingDouble((Suggestion s) -> s.score).reversed()
        .thenComparingInt(s -> Math.abs(s.value.length() - target.length()))
        .thenComparing(s -> s.value));

    if (scored.isEmpty()) return null;

    Suggestion top = scored.get(0);
    double topScore = top.score;
    double runnerUp = scored.size() > 1 ? scored.get(1).score : -1;

    // Confidence rule: strong absolute score AND clear margin over runner-up.
    boolean strongEnough = topScore >= STRONG_SIM;
    boolean clearMargin = (runnerUp < 0) || (topScore - runnerUp >= MARGIN);

    top.isConfident = strongEnough && clearMargin;
    return top;
  }

  // ---- Similarity helpers -----------------------------------------------------

  /** Normalized similarity in [0,1] via Levenshtein edit distance. */
  private static double normalizedLevenshtein(String a, String b) {
    if (a.equals(b)) return 1.0;
    int max = Math.max(a.length(), b.length());
    if (max == 0) return 1.0;
    int d = levenshtein(a, b);
    return 1.0 - (d / (double) max);
  }

  /** Classic O(n*m) Levenshtein; small and dependency-free. */
  private static int levenshtein(String a, String b) {
    int n = a.length(), m = b.length();
    if (n == 0) return m;
    if (m == 0) return n;

    int[] prev = new int[m + 1];
    int[] curr = new int[m + 1];

    for (int j = 0; j <= m; j++) prev[j] = j;

    for (int i = 1; i <= n; i++) {
      curr[0] = i;
      char ca = a.charAt(i - 1);
      for (int j = 1; j <= m; j++) {
        char cb = b.charAt(j - 1);
        int cost = (ca == cb) ? 0 : 1;
        curr[j] = Math.min(
            Math.min(curr[j - 1] + 1, prev[j] + 1),
            prev[j - 1] + cost
        );
      }
      int[] tmp = prev; prev = curr; curr = tmp;
    }
    return prev[m];
  }

  private static boolean isAllLower(String s) {
    if (s.isEmpty()) return false;
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (Character.isLetter(c) && !Character.isLowerCase(c)) return false;
    }
    return true;
  }

  private static boolean isAllUpper(String s) {
    if (s.isEmpty()) return false;
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (Character.isLetter(c) && !Character.isUpperCase(c)) return false;
    }
    return true;
  }

  private static double clamp01(double x) {
    return (x < 0) ? 0 : (x > 1 ? 1 : x);
  }

  private static final class Suggestion {
    final String value;
    final double score;
    boolean isConfident;
    Suggestion(String value, double score) { this.value = value; this.score = score; }
  }
}