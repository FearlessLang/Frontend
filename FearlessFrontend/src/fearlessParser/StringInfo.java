package fearlessParser;

import java.util.*;
import java.util.function.BiConsumer;

import metaParser.Message;
import utils.Bug;

public class StringInfo{
  final int hashCount;
  final List<String> parts= new ArrayList<>();
  final List<String> inter= new ArrayList<>();
  final List<Integer> starts= new ArrayList<>();
  final int line;
  final int col;
  public interface RangeMsg{ void accept(int from, int to, String msg); }
  StringInfo(Token tok, BiConsumer<Integer,Integer> onNoClose, BiConsumer<Integer,Integer> onNoOpen, BiConsumer<Integer,Integer> onMoreOpen, RangeMsg onBadUnicode){
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
    assert q == '\'' || q == '"' : "Expected ' or \" after '|'";
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
      dispatchPayLoad(payload,nextOpen + h + 2 + h, onBadUnicode);
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
  void dispatchPayLoad(String payload, int next, RangeMsg onBadUnicode){
    if (!payload.isEmpty() && payload.charAt(0) == '\\'){
      var decoded= new PayloadParsing(next,payload,onBadUnicode).of();
      if (decoded!=null){ addToLast(parts, decoded); return; }
    }
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
//Parses payloads like: \ uE9\ u1F680\ u915\ u93F...
final class PayloadParsing {
  private final String s;
  private int i= 0;
  final private int startIndex;
  private int lastTokStart= 0;
  final StringInfo.RangeMsg onBadUnicode;
  private final StringBuilder out= new StringBuilder();
  PayloadParsing(int startIndex,String s, StringInfo.RangeMsg onBadUnicode){
    this.startIndex= startIndex;
    this.s= s;
    this.onBadUnicode= onBadUnicode;
    }
  String of(){
    while (i < s.length()){ readUVarToken(); }
    return out.toString();
  }
  RuntimeException report(int fromRel, int size, String msg){
    onBadUnicode.accept(startIndex + fromRel, startIndex + fromRel + size, msg);
    return Bug.unreachable();
  }
  private void readUVarToken(){
    lastTokStart = i;
    if (!match('\\') || !match('u')){
      throw report(lastTokStart, 1, "Unicode run must start with \\u.\nFound "+Message.displayChar(s.charAt(i)));
    }
    int cp= readHex1to6();
    if (cp < 0){
      if (cp == -10){ throw report(lastTokStart, 2, "Missing 1..6 hex digits after \\u"); }
      if (cp == -100){ throw report(lastTokStart, 8, "At most 6 hex digits allowed for \\u"); }
      throw report(lastTokStart, i, "Invalid hex digit in \\u. Use 0-9a-fA-F only");
    }
    checkValidScalar(cp);
    out.append(Character.toChars(cp));
  }
  private boolean match(char c){
    if (i < s.length() && s.charAt(i) == c){ i++; return true; }
    return false;
  }
  private int readHex1to6(){
    int cp= 0;
    int digits= 0;
    while (i < s.length()){
      int v= hexVal(s.charAt(i));
      if (v < 0){ break; }
      if (digits == 6){ return -100; }
      cp = (cp << 4) | v;
      i++;
      digits++;
    }
    if (digits == 0){ return -10; }
    return cp;
  }
  private void checkValidScalar(int cp){
    if (cp >= 0xD800 && cp <= 0xDFFF){
      throw report(lastTokStart, 2, "Surrogate half not allowed; write the scalar code point instead");
    }
    if (cp > 0x10FFFF){
      report(lastTokStart, i, "Code point > 0x10FFFF is invalid");
    }    
  }
  private static int hexVal(char c){
    if (c >= '0' && c <= '9'){ return c - '0'; }
    if (c >= 'a' && c <= 'f'){ return 10 + (c - 'a'); }
    if (c >= 'A' && c <= 'F'){ return 10 + (c - 'A'); }
    return -1;
  }
}