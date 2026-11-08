package fuzz;

import java.util.List;
import java.util.Random;
import java.util.TreeMap;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;
import java.util.stream.IntStream;
import java.util.stream.Stream;

final class Mutations{
  static final int perSeed= 9;
  static final List<String> tokens= List.of("{", "}", "(", ")", "[", "]", ":", ";", "->", "=", ",",
    "mut ", "read ", "iso ", "imm ", "readH ", "mutH ", "read/imm ", "this", " x", " .m", " .foo", "'self ",
    "::", "A", "B", "X", "_", "*", "**", "base.Void", "#", " +");
  static final List<String> rcs= List.of("mut", "read", "imm", "iso", "readH", "mutH");
  static final Pattern rc= Pattern.compile("\\b(mut|read|imm|iso|readH|mutH)\\b");
  static final Pattern word= Pattern.compile("[A-Z]\\w*|\\.[a-z]\\w*|(?<![.\\w])[a-z]\\w*");
  static final String type= "(?:(?:mut|read|imm|iso|readH|mutH) )?[A-Z][\\w.]*(?:\\[[^\\[\\]]*\\])?";
  static final List<Pattern> annotations= Stream.of(
    "\\.[a-z_]\\w*(\\[[^\\[\\]]*\\])",
    "(?<![:\\w.'])("+type+")\\{",
    "[a-z_]\\w*(:"+type+")(?=[,)])",
    "[)\\w](:"+type+")\\s*->",
    "\\b((?:mut|read|imm|iso|readH|mutH) )"
  ).map(Pattern::compile).toList();
  final TreeMap<Integer,String> donors= new TreeMap<>();
  Mutations(List<String> seeds){ for (var s : seeds){ donors.put(s.hashCode(), s); } }
  String mutate(String s, Random r){
    int k= 1 + r.nextInt(3);
    for (int i= 0; i < k && !s.isEmpty(); i += 1){ s = mutateOnce(s, r); }
    return s;
  }
  String mutateOnce(String s, Random r){
    int p= r.nextInt(s.length());
    return switch (r.nextInt(7)){
      case 0 -> deleteCharacters(s, p, r);
      case 1 -> insertToken(s, p, r);
      case 2 -> copySlice(s, p, r);
      case 3 -> insertDonorSlice(s, p, r);
      case 4 -> swapRc(s, r);
      default -> swapWord(s, r);
    };
  }
  static String deleteCharacters(String s, int p, Random r){ return s.substring(0, p) + s.substring(Math.min(s.length(), p+1+r.nextInt(4))); }
  static String insertToken(String s, int p, Random r){ return insert(s, p, tokens.get(r.nextInt(tokens.size()))); }
  static String copySlice(String s, int p, Random r){
    var at= r.nextInt(s.length());
    return insert(s, at, slice(s, p, 1+r.nextInt(12)));
  }
  String insertDonorSlice(String s, int p, Random r){ return insert(s, p, slice(donor(r), r, 20)); }
  String donor(Random r){
    var e= donors.ceilingEntry(r.nextInt());
    return (e == null ? donors.firstEntry() : e).getValue();
  }
  static Stream<String> underAnnotations(String s){
    var rnd= new Random(s.hashCode());
    return IntStream.range(0, perSeed).mapToObj(_ -> underAnnotate(s, rnd));
  }
  static String underAnnotate(String s, Random r){
    int k= 1 + r.nextInt(4);
    for (int i= 0; i < k; i += 1){ s = dropAnnotation(s, r); }
    return s;
  }
  static String dropAnnotation(String s, Random r){
    var byPattern= annotations.stream().map(p -> p.matcher(s).results().toList()).filter(ms -> !ms.isEmpty()).toList();
    if (byPattern.isEmpty()){ return s; }
    var ms= byPattern.get(r.nextInt(byPattern.size()));
    var m= ms.get(r.nextInt(ms.size()));
    return s.substring(0, m.start(1)) + s.substring(m.end(1));
  }
  static boolean annotated(String s){ return annotations.stream().anyMatch(p -> p.matcher(s).find()); }
  static String insert(String s, int at, String t){ return s.substring(0, at) + t + s.substring(at); }
  static String slice(String s, int from, int maxLen){ return s.substring(from, Math.min(s.length(), from+maxLen)); }
  static String slice(String s, Random r, int maxLen){ return slice(s, r.nextInt(s.length()), 1+r.nextInt(maxLen)); }
  static int kind(String w){ return w.startsWith(".") ? 0 : Character.isUpperCase(w.charAt(0)) ? 1 : 2; }
  static String swapWord(String s, Random r){
    var ms= word.matcher(s).results().toList();
    if (ms.isEmpty()){ return s; }
    var m= ms.get(r.nextInt(ms.size()));
    var same= ms.stream().map(MatchResult::group).filter(w -> kind(w) == kind(m.group())).toList();
    return s.substring(0, m.start()) + same.get(r.nextInt(same.size())) + s.substring(m.end());
  }
  static String swapRc(String s, Random r){
    var ms= rc.matcher(s).results().toList();
    if (ms.isEmpty()){ return s; }
    var m= ms.get(r.nextInt(ms.size()));
    return s.substring(0, m.start()) + rcs.get(r.nextInt(rcs.size())) + s.substring(m.end());
  }
}
