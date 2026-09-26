package naming;
import java.util.*;

import core.TName;
import pkgmerge.Package;
import fearlessFullGrammar.T;

public record FreshPrefix(
    Set<String> usedTopTypes,
    Map<String,Integer> topSeq,
    Set<String> allGenericNames,
    Map<TName,OwnerState> owners,
    String pkgName){
  private static final char[] up= "ABCDEFGHJKMNPQRSTUVWXYZ".toCharArray();
  private static final char[] low= "abcdefghjkmnpqrstuvwxyz".toCharArray();
  private record OwnerState(
      Set<String> gen,
      Map<String,Integer> genSeq,
      Set<String> vars,
      Map<String,Integer> varSeq){}
  public FreshPrefix(Package p){
    this(new HashSet<>(),new HashMap<>(),new HashSet<>(),new HashMap<>(),p.name());
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
    String cand= freshCandidate(hint.simpleName(), true, up, topSeq, usedTopTypes, List.of(allGenericNames));
    var res= new TName(pkgName+"."+cand,arity,hint.pos());//all fresh names should start with _ to be pkg private
    aliasOwner(hint,res);
    return res;
  }
  public boolean isFreshGeneric(TName owner,String x){ return !owners.get(owner).gen().contains(x); }
  public String freshGeneric(TName owner,String hint){
    assert pkgName.equals(owner.pkgName());
    var st= owners.get(owner);
    String cand= freshCandidate(hint, true, up, st.genSeq(), st.gen(), List.of(usedTopTypes));
    allGenericNames.add(cand);
    return cand;
  }
  public String freshVar(TName owner,String hint){
    assert pkgName.equals(owner.pkgName());
    var st= owners.get(owner);
    return freshCandidate(hint, false, low, st.varSeq(), st.vars(), List.of());
  }
  // commitScope is checked and updated with the winning candidate; extraChecks are read-only.
  private static String freshCandidate(String hint, boolean type, char[] alphabet,
      Map<String,Integer> seq, Set<String> commitScope, List<Set<String>> extraChecks){
    String base= sanitizeBase(hint, type);
    for (int n= seq.getOrDefault(base, 1);; n++){
      String cand= "_"+encodeBijective(n, alphabet)+base;
      var taken= commitScope.contains(cand) || extraChecks.stream().anyMatch(e->e.contains(cand));
      if (taken){ continue; }
      commitScope.add(cand);
      seq.put(base, n+1);
      return cand;
    }
  }
  public void aliasOwner(TName original,TName alias){// aliasing is deliberate: owner and alias share the same OwnerState
    assert pkgName.equals(original.pkgName());
    assert pkgName.equals(alias.pkgName());
    assert !owners.containsKey(alias);
    owners.put(alias, Objects.requireNonNull(owners.get(original)));
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
    while (n > 0){
      n--;
      sb.append(alphabet[n % base]);
      n/= base;
    }
    return sb.reverse().toString();
  }
}