package fearlessParser;

import java.util.*;
import java.util.function.BiConsumer;

public class StringInfo{
  final int hashCount;
  final List<String> parts= new ArrayList<>();
  final List<String> inter= new ArrayList<>();
  final List<Integer> starts= new ArrayList<>();
  final int line;
  final int col;
  public interface RangeMsg{ void accept(int from, int to, String msg); }
  StringInfo(Token tok, BiConsumer<Integer,Integer> onNoClose, BiConsumer<Integer,Integer> onNoOpen, BiConsumer<Integer,Integer> onMoreOpen){
    this.line= tok.line();
    this.col= tok.column();
    String s= tok.content();
    int n= s.length();
    int i= 0;
    int h= 0;
    while (i < n && s.codePointAt(i) == '#'){ //count leading '#'
      h++;
      i += Character.charCount('#');
    }
    assert i < n && s.codePointAt(i) == '|' : "Expected '|'";
    i += Character.charCount('|');
    assert i < n : "Missing quote after '|'";
    int q = s.codePointAt(i);
    assert q == '`' || q == '"' : "Expected ` or \" after '|'";
    i += Character.charCount(q);
    this.hashCount= h;
    String t= s.substring(i);
    if (h == 0){ parts.add(t); return; }
    String open= "{".repeat(h);
    String close= "}".repeat(h);
    int posCut= 0;
    int posSearch= 0;
    while (true){
      int nextOpen= t.indexOf(open, posSearch);
      int nextClose= t.indexOf(close, posSearch);
      if (nextOpen == -1 && nextClose == -1){ appendParts(t.substring(posCut)); break; }
      if (nextClose == -1){ onNoClose.accept(posCut+1+h,nextOpen+1+h+h); }
      if (nextOpen == -1){ onNoOpen.accept(posCut+1+h,nextClose+1+h+h); }
      if (nextClose < nextOpen){ onNoOpen.accept(posCut+1+h,nextClose+1+h+h); }
      while (t.startsWith("{", nextOpen + h)){ nextOpen += 1; }
      var moreOpen= t.indexOf(open, nextOpen+h, nextClose);
      if (moreOpen != -1){ onMoreOpen.accept(nextOpen+1+h,moreOpen+1+h+h); }
      appendParts(t.substring(posCut, nextOpen));
      String payload= t.substring(nextOpen + h, nextClose);
      dispatchPayLoad(payload,nextOpen + h + 2 + h);
      posCut = nextClose + h;
      while (t.startsWith("}", nextClose + h)){ nextClose += 1; }
      posSearch = nextClose + h;
    }
    assert inter.size() == starts.size();
    assert parts.size() == inter.size() + 1: parts.size()+" "+inter.size();
  }
  void appendParts(String nextStr){
    var add= parts.size() == inter.size();
    if (add){ parts.add(nextStr); return; }
    addToLast(parts,nextStr);
  }
  void dispatchPayLoad(String payload, int next){
    inter.add(payload);
    starts.add(next);  
  }
  static void addToLast(List<String> ss,String s){ ss.set(ss.size() - 1, ss.getLast() + s); }
  static List<String> mergeParts(List<StringInfo> ss){
    final var out= new ArrayList<String>(List.of(""));
    for (var si:ss){
      var p= si.parts;
      addToLast(out, p.get(0));
      for (int i= 1; i < p.size(); i++) out.add(p.get(i));
      addToLast(out,"\n");
    }
    return List.copyOf(out);//because it trims to size too
  }
}