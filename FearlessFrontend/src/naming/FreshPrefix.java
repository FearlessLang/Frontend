package naming;
import java.util.*;

import core.TName;
import pkgmerge.Package;

import static offensiveUtils.Require.*;
import fearlessFullGrammar.T;

public record FreshPrefix(
    Set<String> usedTopTypes,
    Map<String,Integer> topSeq,
    Set<String> allGenericNames,
    Map<TName,OwnerState> owners,
    String pkgName,
    Map<TName,TName> anonSuperT){
  private static final char[] up= "ABCDEFGHJKMNPQRSTUVWXYZ".toCharArray();
  private static final char[] low= "abcdefghjkmnpqrstuvwxyz".toCharArray();
  private static record OwnerState(
      Set<String> gen,
      Map<String,Integer> genSeq,
      Set<String> vars,
      Map<String,Integer> varSeq){}
  public FreshPrefix(Package p){
    this(new HashSet<>(),new HashMap<>(),new HashSet<>(),new HashMap<>(),p.name(),new HashMap<>());
    for (TName tn : p.names().decNames()){ usedTopTypes().add(tn.simpleName()); }
    for (String s : p.map().keySet()){ usedTopTypes().add(s); }
    var xs= p.names().allXs();
    var params= p.names().allParameters();
    assert xs.keySet().equals(params.keySet());
    for (var owner : xs.keySet()){
      var genNames= new HashSet<String>();
      for (T.X x : xs.get(owner)){ genNames.add(x.name()); }
      allGenericNames().addAll(genNames);
      var vars= new HashSet<>(params.get(owner));
      owners().put(owner,new OwnerState(genNames,new HashMap<>(),vars,new HashMap<>()));
    }
  }
  public TName freshTopType(TName hint,int arity){
    String base= sanitizeBase(hint.simpleName(), true);
    int n= topSeq.getOrDefault(base, 1);
    while (true){
      String cand= "_"+encodeBijective(n, up) + base;//all fresh names should start with _ to be pkg private
      var commit= !usedTopTypes.contains(cand) && !allGenericNames.contains(cand);
      if (!commit){ n++; continue; }
      usedTopTypes.add(cand);
      topSeq.put(base, n + 1);
      var res= new TName(pkgName+"."+cand,arity,hint.pos());
      aliasOwner(hint,res);
      return res;
    }
  }
  public void registerAnonSuperT(TName fresh,TName base){ anonSuperT.put(fresh, base); }
  public Optional<TName> anonSuperT(TName t){ return Optional.ofNullable(anonSuperT.get(t)); }
  public boolean isFreshGeneric(TName owner,String x){
    var st= owners.get(owner);
    assert st != null : owner;
    return !st.gen().contains(x);
  }
  public String freshGeneric(TName owner,String hint){
    assert pkgName.equals(owner.pkgName());
    var st= owners.get(owner);
    assert st != null : owner;
    String base= sanitizeBase(hint, true);
    Map<String,Integer> seq= st.genSeq();
    int n= seq.getOrDefault(base, 1);
    Set<String> scope= st.gen();
    while (true){
      String cand= "_" + encodeBijective(n, up) + base;
      var commit= !scope.contains(cand) && !usedTopTypes.contains(cand);
      if (!commit){ n++; continue; }
      scope.add(cand);
      allGenericNames.add(cand);
      seq.put(base, n + 1);
      return cand;
    }
  }
  public String freshVar(TName owner,String hint){
    assert nonNull(owner,hint);
    assert pkgName.equals(owner.pkgName());
    var st= owners.get(owner);
    assert st != null : owner;
    String base= sanitizeBase(hint, false);
    Map<String,Integer> seq= st.varSeq();
    int n= seq.getOrDefault(base, 1);
    Set<String> scope= st.vars();
    while (true){
      String cand= "_" + encodeBijective(n, low) + base;
      if (scope.contains(cand)){ n++; continue; }
      scope.add(cand);
      seq.put(base, n + 1);
      return cand;
    }
  }
  public void aliasOwner(TName original,TName alias){// aliasing is deliberate: owner and alias share the same OwnerState
    assert pkgName.equals(original.pkgName()): pkgName+" -- "+original;
    assert pkgName.equals(alias.pkgName()): pkgName+" -- "+alias;
    var st= owners.get(original);
    assert st != null : original;
    assert !owners.containsKey(alias);
    owners.put(alias, st);
  }
  private static String sanitizeBase(String raw,boolean type){
    String s= raw.replaceAll("[^A-Za-z0-9]", "");
    if (s.isEmpty()){ s= type ? "T" : "v"; }
    if (!Character.isLetter(s.charAt(0))){ s= (type ? "T" : "v") + s; }
    return (s.length() <= 4) ? s : s.substring(0, 4);
  }
  private static String encodeBijective(int n,char[] alphabet){
    int base= alphabet.length;
    StringBuilder sb= new StringBuilder(4);
    int x= n;
    while (x > 0){
      x--;
      sb.append(alphabet[x % base]);
      x/= base;
    }
    return sb.reverse().toString();
  }
}