package fearlessParser;

import java.util.*;

class StringInfo{
  final int hashCount;
  final List<String> parts;
  final List<String> inter;
  StringInfo(String s){
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
    this.parts= new ArrayList<>();
    this.inter= new ArrayList<>();
    String t= s.substring(i);
    if (h == 0){ parts.add(t); return; }
    String open = "{".repeat(h);
    String close = "}".repeat(h);
    int pos= 0;
    while (true){
      int j= t.indexOf(open, pos);
      if (j < 0){ parts.add(t.substring(pos)); break; }
      parts.add(t.substring(pos, j));
      int k = t.indexOf(close, j + open.length());
      assert k >= 0 : "Unclosed interpolation starting at char "+(i+j);
      inter.add(t.substring(j + open.length(), k));
      pos = k + close.length();
    }
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