package message;

import files.Pos;
import static offensiveUtils.Require.*;

import java.util.function.Supplier;

/** Formats source snippets with carets.
 * ASCII only. Columns are 1-based; tabs can be expanded for caret alignment. */
public final class SnippetFormatter{
  private final int contextBefore;
  private final int contextAfter;
  private final boolean showLineNumbers;
  private final int tabWidth; // 0 -> no expansion
  /** If the number of middle lines (strictly between start and end) is > maxMiddleLines,
    * collapse them into an elision line. If <=, print them all. */
  private final int maxMiddleLines;

  private static final int minLineNumberWidth= 3; // always at least 3 digits

  private SnippetFormatter(Builder b){
    this.contextBefore= b.contextBefore;
    this.contextAfter= b.contextAfter;
    this.showLineNumbers= b.showLineNumbers;
    this.tabWidth= b.tabWidth;
    this.maxMiddleLines= b.maxMiddleLines;
  }

  public static Builder builder(){ return new Builder(); }

  public String caret(Supplier<String> s,Span span){
    String src; try {src= s.get();}
    catch (Throwable e){ return s.get().toString(); }
    return caret(src, span);    
  }
  public String caret(String src, Pos p){ return caret(src, Span.of(p, p)); }

  public String caret(String src, Span s){
    assert nonNull(src,s);
    String[] lines= splitLines(src);
    int width= lineNumberWidth(lines.length);
    return s.isSingleLine()
      ? caretSingleLine(lines, s, width)
      : caretMultiLine(lines, s, width);
  }

  private String caretSingleLine(String[] lines, Span s, int width){
    int line= clamp(s.start().line(), 1, lines.length);
    String raw= getLine(lines, line);

    int aCol= Math.max(1, s.start().column());
    int bCol= Math.max(aCol, s.end().column());

    int aVis= tabWidth > 0 ? visualCol(raw, aCol, tabWidth) : aCol;
    int visLen= tabWidth > 0 ? visualDelta(raw, aCol, bCol, tabWidth) : (bCol - aCol);

    StringBuilder sb= new StringBuilder(128);

    appendContextBefore(sb, lines, line, width);
    appendCodeLine(sb, lines, line, width);
    appendCaretLine(sb, raw, aVis, visLen, width);
    appendContextAfter(sb, lines, line, width);

    return sb.toString();
  }

  private String caretMultiLine(String[] lines, Span s, int width){
    int aLine= clamp(s.start().line(), 1, lines.length);
    int bLine= clamp(s.end().line(),   1, lines.length);

    int aCol= Math.max(1, s.start().column());
    int bCol= Math.max(1, s.end().column());

    String rawA= getLine(lines, aLine);
    String rawB= getLine(lines, bLine);

    int aVis= tabWidth > 0 ? visualCol(rawA, aCol, tabWidth) : aCol;
    int bVis= tabWidth > 0 ? visualCol(rawB, bCol, tabWidth) : bCol;

    StringBuilder sb= new StringBuilder(256);

    // start context
    for(int ln= Math.max(1, aLine - contextBefore); ln < aLine; ln++){
      appendCodeLine(sb, lines, ln, width);
    }

    // start line + caret at start col
    appendCodeLine(sb, lines, aLine, width);
    appendCaretLine(sb, rawA, aVis, 0, width);

    // middle
    int mid= Math.max(0, bLine - aLine - 1);
    if(mid > 0){
      if(mid > maxMiddleLines){
        appendElision(sb, mid, width);
      }else{
        for(int ln= aLine + 1; ln <= bLine - 1; ln++){
          appendCodeLine(sb, lines, ln, width);
        }
      }
    }

    // end line + caret at end col
    appendCodeLine(sb, lines, bLine, width);
    appendCaretLine(sb, rawB, bVis, 0, width);

    // end context
    for(int ln= bLine + 1; ln <= Math.min(lines.length, bLine + contextAfter); ln++){
      appendCodeLine(sb, lines, ln, width);
    }
    return sb.toString();
  }

  private void appendContextBefore(StringBuilder sb, String[] lines, int line, int width){
    for(int ln= Math.max(1, line - contextBefore); ln < line; ln++){
      appendCodeLine(sb, lines, ln, width);
    }
  }

  private void appendContextAfter(StringBuilder sb, String[] lines, int line, int width){
    for(int ln= line + 1; ln <= Math.min(lines.length, line + contextAfter); ln++){
      appendCodeLine(sb, lines, ln, width);
    }
  }

  private void appendCodeLine(StringBuilder sb, String[] lines, int oneBased, int width){
    String text= getLine(lines, oneBased);
    if(tabWidth > 0){ text= expandTabs(text, tabWidth); }
    if(!showLineNumbers){ sb.append(text).append('\n'); return; }
    sb.append(padLineNum(oneBased, width)).append('|').append(text).append('\n');
  }

  private void appendCaretLine(StringBuilder sb, String rawLineText, int visualCol, int underlineVisLen, int width){
    int spaces= Math.max(0, visualCol - 1);
    if(showLineNumbers){ sb.append(repeat(' ', width)).append('|'); }
    sb.append(repeat(' ', spaces)).append('^');
    if(underlineVisLen > 0){ sb.append(repeat('~', underlineVisLen)); }
    sb.append('\n');
  }

  private void appendElision(StringBuilder sb, int midLines, int width){
    if(showLineNumbers){ sb.append(repeat(' ', width)).append('|'); }
    sb.append("... ").append(midLines).append(" line");
    if(midLines != 1){ sb.append('s'); }
    sb.append(" ...\n");
  }

  private int lineNumberWidth(int totalLines){
    if(!showLineNumbers){ return 0; }
    int digits= String.valueOf(Math.max(1, totalLines)).length();
    return Math.max(minLineNumberWidth, digits);
  }

  private static String[] splitLines(String s){ return s.split("\\R", -1); }

  private static String getLine(String[] lines, int oneBased){
    return (oneBased < 1 || oneBased > lines.length) ? "" : lines[oneBased - 1];
  }

  private static int clamp(int v, int lo, int hi){ return Math.max(lo, Math.min(hi, v)); }

  private static String padLineNum(int n, int w){
    String s= Integer.toString(Math.max(0, n));
    int k= Math.max(0, w - s.length());
    return repeat('0', k) + s;
  }

  /** Expand tabs to the next tab stop. Column is 1-based. */
  private static String expandTabs(String s, int tabWidth){
    StringBuilder out= new StringBuilder(s.length() + 8);
    int col= 1;
    for(int i= 0; i < s.length(); i++){
      char c= s.charAt(i);
      if(c == '\t'){
        int spaces= tabWidth - ((col - 1) % tabWidth);
        out.append(repeat(' ', spaces));
        col += spaces;
      }else{
        out.append(c);
        col += 1;
      }
    }
    return out.toString();
  }

  /** Visual column (1-based) after rendering characters up to logicalCol-1, expanding tabs. */
  private static int visualCol(String rawLine, int logicalCol, int tabWidth){
    if(logicalCol <= 1 || tabWidth <= 0){ return Math.max(1, logicalCol); }
    int vis= 1;
    int upto= Math.max(1, logicalCol - 1);
    int limit= Math.min(rawLine.length(), upto - 1);
    for(int i= 0; i <= limit; i++){
      char c= rawLine.charAt(i);
      if(c == '\t'){
        int spaces= tabWidth - ((vis - 1) % tabWidth);
        vis += spaces;
      }else{
        vis += 1;
      }
    }
    return vis;
  }

  /** Visual width between startLogicalCol (inclusive) and endLogicalCol (exclusive/inclusive diff used by caller). */
  private static int visualDelta(String rawLine, int startLogicalCol, int endLogicalCol, int tabWidth){
    if(endLogicalCol <= startLogicalCol){ return 0; }
    int a= visualCol(rawLine, startLogicalCol, tabWidth);
    int b= visualCol(rawLine, endLogicalCol, tabWidth);
    return Math.max(0, b - a);
  }

  private static String repeat(char ch, int n){
    if(n <= 0){ return ""; }
    StringBuilder sb= new StringBuilder(n);
    for(int i= 0; i < n; i++){ sb.append(ch); }
    return sb.toString();
  }

  public static final class Builder{
    private int contextBefore= 1;
    private int contextAfter= 1;
    private boolean showLineNumbers= true;
    private int tabWidth= 0;
    private int maxMiddleLines= 0;

    public Builder contextBefore(int v){ this.contextBefore = Math.max(0, v); return this; }
    public Builder contextAfter(int v){ this.contextAfter = Math.max(0, v); return this; }
    public Builder showLineNumbers(boolean v){ this.showLineNumbers = v; return this; }
    public Builder tabWidth(int v){ this.tabWidth = Math.max(0, v); return this; }
    /** Show up to v middle lines within the span; if more exist, collapse them. */
    public Builder maxMiddleLines(int v){ this.maxMiddleLines = Math.max(0, v); return this; }

    public SnippetFormatter build(){ return new SnippetFormatter(this); }
  }
}