package pkgmerge;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import core.TName;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.T;
import message.WellFormednessErrors;

public record DeclaredNames(Set<TName> decNames, Map<TName,Set<T.X>> allXs, Map<TName,Set<String>> allParameters){
  static public DeclaredNames of(String pkgName, List<Declaration> ds, Map<String,String> map){
    var err= new WellFormednessErrors(pkgName);
    var v= new AllDeclaredNames(err);
    ds.forEach(d->v.visitTopDeclaration(d,pkgName));
    var allDecs= Collections.unmodifiableSet(v.decNames);
    var allXs= Collections.unmodifiableMap(v.Xs);
    var disj= Collections.disjoint(allDecs.stream().map(tn->tn.s()).toList(),map.keySet());
    if (!disj){ throw err.usedDeclaredNameClash(pkgName,allDecs,map.keySet()); }    
    var allNames= Stream.concat(allDecs.stream().map(tn->tn.s()), map.keySet().stream()).toList();
    var mergeAllXs= allXs.values().stream().flatMap(Set::stream).map(X->X.name()).toList();
    var disjXs= Collections.disjoint(allNames,mergeAllXs);
    if (!disjXs){ throw err.genericTypeVariableShadowTName(pkgName,allXs,allNames,map.keySet()); }
    return new DeclaredNames(allDecs,allXs,Collections.unmodifiableMap(v.xs));
  }
}