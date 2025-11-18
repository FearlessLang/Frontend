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
 *      "Did you mean "foo" ?"
 *  - If suggestions are ambiguous or weak, we show only the "In scope" line
 *    (if any) and skip the "Did you mean" line to avoid misleading hints.
 */
public final class NameSuggester {
  /** If there are this many or fewer names, show the "In scope:" line. */
  private static final int maxScopeToList= 12;
  /** Strong similarity threshold (normalized 0..1). */
  private static final double strongSimilarity= 0.68;
  /** Extra bonus for same first letter (helps stabilize top-1). */
  private static final double sameFirstBonus= 0.03;
  /** Require top-1 to beat top-2 by at least this margin to avoid ambiguity. */
  private static final double margin= 0.08;
  
  private NameSuggester() {}
  public static Optional<String> bestName(String name, List<String> candidates){
    assert ! (name == null || name.isEmpty() || candidates == null);
    if (candidates.isEmpty()){ return Optional.empty(); }
    return bestSuggestion(name, candidates).map(s -> s.value);
  }
  public static Optional<String> suggest(String name, List<String> candidates){
    StringBuilder out= new StringBuilder();
    bestName(name, candidates)
      .ifPresent(best -> out.append("Did you mean ").append(Message.displayString(best)).append(" ?\n"));
    if (candidates.size() <= maxScopeToList){out
      .append("In scope: ")
      .append(candidates.stream().map(Message::displayString).collect(Collectors.joining(", ")))
      .append(".\n");
    }
    if (out.length() == 0){ return Optional.empty(); }
    if (out.charAt(out.length() - 1) == '\n'){ out.setLength(out.length() - 1); }
    return Optional.of(out.toString());
  }
  private static Optional<Suggestion> bestSuggestion(String target, List<String> candidates){
    if (candidates.isEmpty()){ return Optional.empty(); }
    Suggestion best= pickBest(target, candidates);
    if (best == null || !best.isConfident){ return Optional.empty(); }
    return Optional.of(best);
  }
  private static Suggestion pickBest(String target, List<String> candidates) {
    String t= target;
    boolean tLower= isAllLower(t);
    boolean tUpper= isAllUpper(t);

    List<Suggestion> scored= new ArrayList<>(candidates.size());
    for (String c : candidates) {
      double base= normalizedLevenshtein(t, c);
      var applyBonus= !t.isEmpty() && !c.isEmpty()
        && Character.toLowerCase(t.charAt(0)) == Character.toLowerCase(c.charAt(0));
      if (applyBonus){ base += sameFirstBonus; }
      var isSimilarCase= (tLower && isAllLower(c)) || (tUpper && isAllUpper(c));
      if (isSimilarCase){ base += 0.01; }
      double score= clamp01(base);
      scored.add(new Suggestion(c, score));
    }
    if (scored.isEmpty()){ return null; }
    scored.sort(Comparator
      .comparingDouble((Suggestion s) -> s.score).reversed()
      .thenComparingInt(s -> Math.abs(s.value.length() - target.length()))
      .thenComparing(s -> s.value));

    Suggestion top= scored.get(0);
    double topScore= top.score;
    double runnerUp= scored.size() > 1 ? scored.get(1).score : -1;
    boolean strongEnough= topScore >= strongSimilarity;
    boolean clearMargin= (runnerUp < 0) || (topScore - runnerUp >= margin);
    top.isConfident = strongEnough && clearMargin;
    return top;
  }
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
    int n= a.length();
    int m= b.length();
    if (n == 0){ return m; }
    if (m == 0){ return n; }

    int[] prev= new int[m + 1];
    int[] curr= new int[m + 1];

    for (int j= 0; j <= m; j++){ prev[j] = j; }

    for (int i= 1; i <= n; i++){
      curr[0] = i;
      char ca = a.charAt(i - 1);
      for (int j = 1; j <= m; j++) {
        char cb = b.charAt(j - 1);
        int cost = (ca == cb) ? 0 : 1;
        curr[j] = Math.min(Math.min(curr[j - 1] + 1, prev[j] + 1), prev[j - 1] + cost);
      }
      int[] tmp = prev;
      prev = curr;
      curr = tmp;
    }
    return prev[m];
  }
  private static boolean isAllLower(String s){
    if (s.isEmpty()){ return false; }
    for (int i= 0; i < s.length(); i++) {
      char c= s.charAt(i);
      if (Character.isLetter(c) && !Character.isLowerCase(c)){ return false; }
    }
    return true;
  }
  private static boolean isAllUpper(String s) {
    if (s.isEmpty()){ return false; }
    for (int i= 0; i < s.length(); i++) {
      char c= s.charAt(i);
      if (Character.isLetter(c) && !Character.isUpperCase(c)){ return false; }
    }
    return true;
  }
  private static double clamp01(double x){ return (x < 0) ? 0 : (x > 1 ? 1 : x); }

  private static final class Suggestion {
    final String value;
    final double score;
    boolean isConfident;
    Suggestion(String value, double score) { this.value = value; this.score = score; }
  }
}