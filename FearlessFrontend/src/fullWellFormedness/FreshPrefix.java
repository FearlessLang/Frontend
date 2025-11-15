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
      var names= new HashSet<String>();
      for (var x : e.getValue()){ names.add(x.name()); }
      usedGen.put(e.getKey(), names);
      allGenericNames.addAll(names);
    }
    for (var e : p.names().allParameters().entrySet()){
      usedVar.put(e.getKey(), new HashSet<>(e.getValue()));
    }
    assert usedGen.keySet().equals(usedVar.keySet());
    for (TName owner : usedGen.keySet()){
      genSeq.put(owner, new HashMap<>());
      varSeq.put(owner, new HashMap<>());
    }
  }
  public TName freshTopType(TName hint, int arity){
    assert nonNull(hint);
    String base= sanitizeBase(hint.simpleName(), true);
    int n= topSeq.getOrDefault(base, 1);
    while (true){
      String cand= encodeBijective(n, up) + "_" + base;
      var commit= !usedTopTypes.contains(cand) && !allGenericNames.contains(cand);
      if (!commit){ n++; continue; }
      usedTopTypes.add(cand);
      topSeq.put(base, n + 1);
      var res= new TName(pkgName+"."+cand,arity,hint.pos());
      aliasOwner(hint,res);
      return res;
    }
  }
  public boolean isFreshGeneric(TName owner, String x){//used where we know it is a valid generic elsewhere (so already not a top type)
    Set<String> scope= usedGen.get(owner);
    assert scope != null : owner;
    return !scope.contains(x);// && !usedTopTypes.contains(x.name());
  }
  public String freshGeneric(TName owner, String hint){
    assert nonNull(owner,hint);
    assert pkgName.equals(owner.pkgName());
    String base= sanitizeBase(hint, true);
    Map<String,Integer> seq= genSeq.get(owner);
    int n= seq.getOrDefault(base, 1);
    Set<String> scope= usedGen.get(owner);
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
    assert pkgName.equals(owner.pkgName());
    String base= sanitizeBase(hint, false);
    Map<String,Integer> seq= varSeq.get(owner);
    int n= seq.getOrDefault(base, 1);
    Set<String> scope= usedVar.get(owner);
    while (true){
      String cand = encodeBijective(n, low) + "_" + base;
      if (scope.contains(cand)){ n++; continue; }
      scope.add(cand);
      seq.put(base, n + 1);
      return cand;
    }
  }
  //Aliasing is deliberate to keep in sink:
  //we may add new type/names/generics to the outer or the inner,
  //and they both need to know about it to avoid those names.
  //They are contained into each other, so to avoid all kinds of hiding,
  //they need to avoid each other names in addition to their own.
  public void aliasOwner(TName original, TName alias){
    assert nonNull(original, alias);
    assert pkgName.equals(original.pkgName()): pkgName+" -- "+original;
    assert pkgName.equals(alias.pkgName()): pkgName+" -- "+alias;
    var gen= usedGen.get(original);
    var vars= usedVar.get(original);
    var gSeq = genSeq.get(original);
    var vSeq = varSeq.get(original);
    assert nonNull(gen,vars,gSeq,vSeq);
    assert !usedGen.containsKey(alias) && !usedVar.containsKey(alias);
    usedGen.put(alias, gen);
    usedVar.put(alias, vars);      
    genSeq.put(alias, gSeq);
    varSeq.put(alias, vSeq);
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