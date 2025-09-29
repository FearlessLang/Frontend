package metaParser;

import java.net.URI;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;

public record Message(String msg,int priority){

  // Rendering constants (mirrors SnippetFormatter defaults you liked)
  private static final int TAB_WIDTH = 4;
  private static final int MIN_LN_WIDTH = 3;

  /** Build the final single-string error message (lines 1..11 as per spec). */
  public static String of(Function<URI,String> loader, List<Frame> frames, String msg){
    if (frames == null || frames.isEmpty()) return msg;

    // 1) containment (bottom-up clamp)
    List<Frame> contained = ensureContainment(frames);

    // 2) invisibleCharacters trimming (shrink both ends to visible)
    List<Frame> visible = trimInvisible(loader, contained);

    // 3) grouping (pick up to 3 single-line spans + first multiline)
    Grouping g = group(visible);

    // Source + precomputed line-number width
    String src = Objects.requireNonNull(loader.apply(g.file()));
    String[] lines = splitLines(src);
    int width = lineNumberWidth(lines.length);

    // 4) single-line caret (on caretLine) using - ~ ^ for outer/mid/inner
    String caretLine = makeCaretLine(lines, g, width);

    // 5) final 6-line (or 2-line) render
    String body = (g.multiLine() != null)
      ? renderSix(lines, g, width, caretLine)
      : renderTwo(lines, g, width, caretLine);

    // Header (line 1), blank (line 2)
    String header = "In file: " + PrettyFileName.displayFileName(g.file());

    String framesLine = "While inspecting " + frames.stream()
      .filter(f->!f.name().isBlank()).map(Frame::name)
      .collect(Collectors.joining(" > "));

    // Lines 1..(8 or 4) as specified; FearlessException.render() appends line 11 (the code).
    // We also insert the blank separator above the frames line.
    return header + "\n\n" + body + "\n\n" + framesLine + "\n" + msg;
  }

  // ===== Phase 1: containment ===================================================

  private static List<Frame> ensureContainment(List<Frame> fs){
    ArrayList<Frame> out = new ArrayList<>(fs);
    if (out.size() <= 1) return List.copyOf(out);
    for (int i = out.size() - 2; i >= 0; i--){
      Span inner = out.get(i).s();
      Span container = out.get(i+1).s();
      out.set(i, new Frame(out.get(i).name(), clampTo(inner, container)));
    }
    return List.copyOf(out);
  }
  private static Span clampTo(Span s, Span c){
    int sL = Math.max(s.startLine(), c.startLine());
    int eL = Math.min(s.endLine(),   c.endLine());
    if (sL > eL){ sL = c.startLine(); eL = c.startLine(); }

    int sC = (sL==s.startLine()&&sL==c.startLine()) ? Math.max(s.startCol(), c.startCol())
             : (sL==c.startLine() ? c.startCol() : s.startCol());
    int eC = (eL==s.endLine()&&eL==c.endLine()) ? Math.min(s.endCol(), c.endCol())
             : (eL==c.endLine() ? c.endCol() : s.endCol());
    if (sL == eL && sC > eC) sC = eC;

    return new Span(s.fileName(), sL, Math.max(1, sC), eL, Math.max(1, eC));
  }

  // ===== Phase 2: invisibleCharacters trimming ==================================

  private static List<Frame> trimInvisible(Function<URI,String> loader, List<Frame> fs){
    ArrayList<Frame> out = new ArrayList<>(fs.size());
    for (Frame f : fs){
      Span v = shrinkToVisible(loader, f.s());
      out.add(new Frame(f.name(), v));
    }
    return List.copyOf(out);
  }
  private static Span shrinkToVisible(Function<URI,String> loader, Span s){
    String src = Objects.requireNonNull(loader.apply(s.fileName()));
    String[] lines = splitLines(src);

    Pos a = nextVisible(lines, new Pos(s.startLine(), s.startCol()), new Pos(s.endLine(), s.endCol()));
    Pos b = prevVisible(lines, a, new Pos(s.endLine(), s.endCol()));
    return new Span(s.fileName(), a.line, a.col, b.line, b.col);
  }
  private static Pos nextVisible(String[] lines, Pos p, Pos limit){
    int line = clamp(p.line, 1, lines.length), col = Math.max(1, p.col);
    while (beforeOrEqual(line, col, limit)){
      String ln = get(lines, line);
      if (col <= ln.length()){
        char ch = ln.charAt(col - 1);
        if (isVisible(ch)) return new Pos(line, col);
        col++;
      } else { line++; col = 1; }
    }
    return limit;
  }
  private static Pos prevVisible(String[] lines, Pos start, Pos p){
    int line = clamp(p.line, 1, lines.length), col = Math.max(1, p.col);
    while (afterOrEqual(line, col, start)){
      String ln = get(lines, line);
      if (col >= 1){
        if (col <= ln.length()){
          char ch = ln.charAt(col - 1);
          if (isVisible(ch)) return new Pos(line, col);
        }
        col--;
        if (col < 1){ line--; if (line < start.line) break; col = Math.max(1, get(lines, line).length()); }
      }
    }
    return new Pos(start.line, start.col);
  }
  private static boolean isVisible(char c){ return c!=' ' && c!='\t' && c!='\n' && c!='\r'; }

  // ===== Phase 3: grouping =======================================================

  private record Grouping(URI file, List<Span> singles, Span multiLine, int caretLine){}

  private static Grouping group(List<Frame> fs){
    List<Span> spans = fs.stream().map(Frame::s).toList();
    URI file = spans.getLast().fileName();

    // Take initial chain of single-line spans, but only those on the same line as the innermost single.
    ArrayList<Span> leadingSingles = new ArrayList<>();
    for (Span s : spans){ if (s.isSingleLine()) leadingSingles.add(s); else break; }
    if (!leadingSingles.isEmpty()){
      int targetLine = leadingSingles.getLast().startLine();
      leadingSingles.removeIf(s -> s.startLine() != targetLine || !s.isSingleLine());
    }

    // If <=3, keep all; else keep first, a middle near avg size, and last — sort outer..inner by length.
    List<Span> chosenSingles = pickUpToThree(leadingSingles);

    // First multiline after singles (if any)
    Span firstMulti = null;
    for (int i = leadingSingles.size(); i < spans.size(); i++){
      if (!spans.get(i).isSingleLine()){ firstMulti = spans.get(i); break; }
    }

    int caretLine = !chosenSingles.isEmpty() ? chosenSingles.getLast().startLine()
                   : (firstMulti != null ? firstMulti.startLine() : spans.getLast().startLine());

    return new Grouping(file, chosenSingles, firstMulti, caretLine);
  }

  private static List<Span> pickUpToThree(List<Span> singles){
    if (singles.size() <= 3) return List.copyOf(singles);
    Span first = singles.getFirst(), last = singles.getLast();
    double avg = (lenInclusive(first) + lenInclusive(last)) / 2.0;
    Span mid = singles.subList(1, singles.size()-1).stream()
      .min(Comparator.comparingDouble(s -> Math.abs(lenInclusive(s) - avg)))
      .orElse(singles.get(1));
    ArrayList<Span> out = new ArrayList<>(3);
    out.add(first); out.add(mid); out.add(last);
    out.sort(Comparator.comparingInt(Message::lenInclusive).reversed()); // outer (-), middle (~), inner (^)

    return List.copyOf(out);
  }
  private static int lenInclusive(Span s){ return Math.max(1, s.endCol() - s.startCol() + 1); }

  // ===== Phase 4: caret line construction =======================================

  private static String makeCaretLine(String[] lines, Grouping g, int width){
    String raw = get(lines, g.caretLine());
    String display = expandTabs(raw, TAB_WIDTH);
    char[] carr = new char[Math.max(1, display.length())];
    for (int i=0;i<carr.length;i++) carr[i] = ' ';

    // Marks in outer..inner order
    char[] marks = new char[]{'-', '~', '^'};
    List<Span> sps = g.singles();
    for (int i = 0; i < Math.min(3, sps.size()); i++){
      Span s = sps.get(i);
      int aVis = visualCol(raw, s.startCol(), TAB_WIDTH);
      int len  = visualDelta(raw, s.startCol(), s.endCol(), TAB_WIDTH);
      int a = clamp(aVis, 1, carr.length);
      int b = clamp(aVis + Math.max(0, len) - 1, 1, carr.length); // inclusive right edge
      for (int c = a; c <= b; c++){ carr[c-1] = marks[i]; }
    }
    return repeat(' ', width) + '|' + ' ' + new String(carr);
  }

  // ===== Phase 5: final rendering ===============================================

  /** 6-line render when a multiline span exists. */
  private static String renderSix(String[] lines, Grouping g, int width, String caretLine){
    Span group = g.multiLine();
    // Lines: 1) group start (left-trim to group start), 2) skipped before caret,
    // 3) caret line text, 4) caret, 5) skipped after caret, 6) group end (right-trim to end)
    String l1 = lineWithLeftPad(lines, group.startLine(), width, group.startCol());
    String l2 = elided(width, g.caretLine() - group.startLine() - 1);
    String l3 = numbered(lines, g.caretLine(), width);
    String l4 = caretLine;
    String l5 = elided(width, group.endLine() - g.caretLine() - 1);
    String l6 = lineRightTrim(lines, group.endLine(), width, group.endCol());
    return String.join("\n", l1, l2, l3, l4, l5, l6);
  }

  /** 2-line render fallback when there is no multiline span. */
  private static String renderTwo(String[] lines, Grouping g, int width, String caretLine){
    String l1 = numbered(lines, g.caretLine(), width);
    String l2 = caretLine;
    return l1 + "\n" + l2;
  }

  // ----- numbered code line helpers ---------------------------------------------

  private static String numbered(String[] lines, int lineNum, int width){
    String raw = get(lines, lineNum);
    String display = expandTabs(raw, TAB_WIDTH);
    return padLineNum(lineNum, width) + '|' + ' ' + display;
  }
  private static String lineWithLeftPad(String[] lines, int lineNum, int width, int startCol){
    String raw = get(lines, lineNum);
    String display = expandTabs(raw, TAB_WIDTH);
    int visStart = visualCol(raw, startCol, TAB_WIDTH);
    int keepFrom = Math.max(1, Math.min(visStart, display.length())); // visual index (1-based)
    String leftSpaces = repeat(' ', keepFrom - 1);
    String rest = (keepFrom - 1 < display.length()) ? display.substring(keepFrom - 1) : "";
    return padLineNum(lineNum, width) + '|' + ' ' + leftSpaces + rest;
  }
  private static String lineRightTrim(String[] lines, int lineNum, int width, int endCol){
    String raw = get(lines, lineNum);
    String display = expandTabs(raw, TAB_WIDTH);
    int visEnd = visualCol(raw, endCol, TAB_WIDTH); // caret draws at this col; content up to visEnd
    int to = Math.max(0, Math.min(visEnd, display.length()));
    String cut = display.substring(0, to);
    return padLineNum(lineNum, width) + '|' + ' ' + cut;
  }
  private static String elided(int width, int count){
    return repeat(' ', width) + '|' + ' ' + "... " + Math.max(0, count) + " line" + (count==1 ? " ..." : "s ...");
  }

  // ===== small helpers (split, lines, visual columns, padding) ==================

  private static String[] splitLines(String s){ return s.split("\\R", -1); }
  private static String get(String[] lines, int oneBased){
    if (oneBased < 1 || oneBased > lines.length) return "";
    return lines[oneBased-1];
  }
  private static int clamp(int v, int lo, int hi){ return Math.max(lo, Math.min(hi, v)); }

  private static int lineNumberWidth(int totalLines){
    int digits = String.valueOf(Math.max(1, totalLines)).length();
    return Math.max(MIN_LN_WIDTH, digits);
  }
  private static String padLineNum(int n, int w){
    String s = Integer.toString(Math.max(0, n));
    int k = Math.max(0, w - s.length());
    return repeat('0', k) + s;
  }
  private static String repeat(char c, int n){
    if (n <= 0) return "";
    StringBuilder sb = new StringBuilder(n);
    for (int i=0;i<n;i++) sb.append(c);
    return sb.toString();
  }

  /** Expand tabs into spaces (tab stops every TAB_WIDTH columns). */
  private static String expandTabs(String s, int tabWidth){
    if (tabWidth <= 0 || s.indexOf('\t') < 0) return s;
    StringBuilder out = new StringBuilder(s.length() + 8);
    int col = 1; // 1-based
    for (int i=0;i<s.length();i++){
      char ch = s.charAt(i);
      if (ch == '\t'){
        int spaces = tabWidth - ((col - 1) % tabWidth);
        for (int k=0;k<spaces;k++){ out.append(' '); }
        col += spaces;
      }else{
        out.append(ch);
        col += 1;
      }
    }
    return out.toString();
  }

  /** Visual column (1-based) at a logical column (expands tabs). */
  private static int visualCol(String rawLine, int logicalCol, int tabWidth){
    if (logicalCol <= 1 || tabWidth <= 0) return Math.max(1, logicalCol);
    int vis = 1;
    int uptoExclusive = Math.max(0, logicalCol - 1);
    int limit = Math.min(uptoExclusive, rawLine.length());
    for (int i = 0; i < limit; i++){
      char ch = rawLine.charAt(i);
      if (ch == '\t'){
        int spaces = tabWidth - ((vis - 1) % tabWidth);
        vis += spaces;
      }else{
        vis += 1;
      }
    }
    return Math.max(1, vis);
  }

  private static int visualDelta(String rawLine, int startCol, int endCol, int tabWidth){
    int aIdx = Math.max(0, startCol - 1);
    int bIdxInclusive = Math.max(aIdx, Math.min(endCol - 1, Math.max(0, rawLine.length() - 1)));
    if (rawLine.isEmpty() || aIdx > bIdxInclusive) return 0;
    int vis = 0;
    for (int i = aIdx; i <= bIdxInclusive; i++){
      char ch = rawLine.charAt(i);
      if (ch == '\t'){
        int spaces = tabWidth - ((vis) % tabWidth); // vis is 0-based width so far
        vis += spaces;
      }else{
        vis += 1;
      }
    }
    return Math.max(0, vis);
  }

  private static boolean beforeOrEqual(int l, int c, Pos limit){
    return l < limit.line || (l == limit.line && c <= limit.col);
  }
  private static boolean afterOrEqual(int l, int c, Pos start){
    return l > start.line || (l == start.line && c >= start.col);
  }
  private record Pos(int line, int col){}
}
