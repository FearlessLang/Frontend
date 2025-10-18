package fullWellFormedness;
import java.util.*;

import fearlessFullGrammar.TName;
import static offensiveUtils.Require.*;

public final class FreshPrefix {
  private static final char[] up= "ABCDEFGHJKMNPQRSTUVWXYZ".toCharArray();
  private static final char[] low= "abcdefghjkmnpqrstuvwxyz".toCharArray();
  private final Set<String> usedTopTypes= new HashSet<>();
  private final Map<String,Integer> topSeq= new HashMap<>();
  private final Set<String> allGenericNames= new HashSet<>();
  private final Map<TName, Set<String>> usedGen= new HashMap<>();
  private final Map<TName, Map<String,Integer>> genSeq= new HashMap<>();
  private final Map<TName, Set<String>> usedVar= new HashMap<>();
  private final Map<TName, Map<String,Integer>> varSeq= new HashMap<>();
  private final String pkgName;
  public FreshPrefix(Package p){
    pkgName= p.name();
    for (TName tn : p.names().decNames()){ usedTopTypes.add(tn.simpleName()); }
    for (String s: p.map().keySet()){ usedTopTypes.add(s); }
    for (var e : p.names().allXs().entrySet()){
      var owner= e.getKey();
      var names= new HashSet<String>();
      for (var x : e.getValue()){ names.add(x.name()); }
      usedGen.put(owner, names);
      allGenericNames.addAll(names);
    }
    for (var e : p.names().allParameters().entrySet()){
      usedVar.put(e.getKey(), new HashSet<>(e.getValue()));
    }    
  }
  public TName freshTopType(TName hint){
    assert nonNull(hint);
    String base= sanitizeBase(hint.simpleName(), true);
      int n= topSeq.getOrDefault(base, 1);
      while (true){
        String cand= encodeBijective(n, up) + "_" + base;
        var commit= !usedTopTypes.contains(cand) && !allGenericNames.contains(cand);
        if (!commit){ n++; continue; }
        usedTopTypes.add(cand);
        topSeq.put(base, n + 1);
        return new TName(pkgName+"."+cand,hint.arity(),"",hint.pos());
      }
    }
    public String freshGeneric(TName owner, String hint) {
      assert nonNull(owner,hint);
      String base= sanitizeBase(hint, true);
      Map<String,Integer> seq= genSeq.computeIfAbsent(owner, _ -> new HashMap<>());
      int n= seq.getOrDefault(base, 1);
      Set<String> scope= usedGen.computeIfAbsent(owner, _ -> new HashSet<>());
      while (true){
        String cand= encodeBijective(n, up) + "_" + base;
        var commit= !scope.contains(cand) && !usedTopTypes.contains(cand);
        if (!commit){ n++; continue; }
        scope.add(cand);
        allGenericNames.add(cand);
        seq.put(base, n + 1);
        return cand;
      }
    }
    public String freshVar(TName owner, String hint) {
      assert nonNull(owner,hint);
      String base= sanitizeBase(hint, false);
      Map<String,Integer> seq= varSeq.computeIfAbsent(owner, _ -> new HashMap<>());
      int n= seq.getOrDefault(base, 1);
      Set<String> scope= usedVar.computeIfAbsent(owner, _ -> new HashSet<>());
      while (true){
        String cand = encodeBijective(n, low) + "_" + base;
        if (scope.contains(cand)){ n++; continue; }
        scope.add(cand);
        seq.put(base, n + 1);
        return cand;
      }
    }
    private static String sanitizeBase(String raw, boolean type) {
      String s= raw.replaceAll("[^A-Za-z0-9_]", "");
      if (s.isEmpty()){ s = type ? "T" : "v"; }
      if (!Character.isLetter(s.charAt(0))){ s = (type ? "T" : "v") + s; }
      return (s.length() <= 4) ? s : s.substring(0, 4);
    }
    private static String encodeBijective(int n, char[] alphabet){
      int base= alphabet.length;
      StringBuilder sb= new StringBuilder(4);
      int x= n;
      while (x > 0){
        x--;
        sb.append(alphabet[x % base]);
        x /= base;
      }
      return sb.reverse().toString();
    }
  }