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
  public static DeclaredNames of(String pkgName, List<Declaration> ds, Map<String,String> map){
    var err= new WellFormednessErrors(pkgName);
    var v= new AllDeclaredNames(err);
    ds.forEach(d->v.visitTopDeclaration(d,pkgName));
    var allDecs= Collections.unmodifiableSet(v.decNames);
    var allXs= Collections.unmodifiableMap(v.Xs);
    var decStrs= allDecs.stream().map(TName::s).toList();
    if (!Collections.disjoint(decStrs,map.keySet())){ throw err.usedDeclaredNameClash(pkgName,allDecs,map.keySet()); }
    var allNames= Stream.concat(decStrs.stream(), map.keySet().stream()).toList();
    var mergeAllXs= allXs.values().stream().flatMap(Set::stream).map(T.X::name).toList();
    var disjXs= Collections.disjoint(allNames,mergeAllXs);
    if (!disjXs){ throw err.genericTypeVariableShadowTName(pkgName,allXs,allNames,map.keySet()); }
    return new DeclaredNames(allDecs,allXs,Collections.unmodifiableMap(v.xs));
  }
}