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
    String cand= freshCandidate(hint.simpleName(), true, up, topSeq, usedTopTypes, List.of(allGenericNames));
    var res= new TName(pkgName+"."+cand,arity,hint.pos());//all fresh names should start with _ to be pkg private
    aliasOwner(hint,res);
    return res;
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
    String cand= freshCandidate(hint, true, up, st.genSeq(), st.gen(), List.of(usedTopTypes));
    allGenericNames.add(cand);
    return cand;
  }
  public String freshVar(TName owner,String hint){
    assert nonNull(owner,hint);
    assert pkgName.equals(owner.pkgName());
    var st= owners.get(owner);
    assert st != null : owner;
    return freshCandidate(hint, false, low, st.varSeq(), st.vars(), List.of());
  }
  // commitScope is checked and updated with the winning candidate; extraChecks are read-only.
  private static String freshCandidate(String hint, boolean type, char[] alphabet,
      Map<String,Integer> seq, Set<String> commitScope, List<Set<String>> extraChecks){
    String base= sanitizeBase(hint, type);
    int n= seq.getOrDefault(base, 1);
    outer:
    while (true){
      String cand= "_"+encodeBijective(n, alphabet)+base;
      if (commitScope.contains(cand)){ n++; continue; }
      for (Set<String> extra : extraChecks){
        if (extra.contains(cand)){ n++; continue outer; }
      }
      commitScope.add(cand);
      seq.put(base, n+1);
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