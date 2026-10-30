package pkgmerge;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import core.T;
import core.TName;
import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import inference.E;
import message.WellFormednessErrors;
import utils.Join;

public record Package(String name, Map<String,String> map, Map<String,String> writtenIn, List<FileFull.Use> uses, List<Declaration> decs, DeclaredNames names, Logger log){
  public WellFormednessErrors err(){ return new WellFormednessErrors(name, map, writtenIn, new LinkedHashSet<>()); }
  public static Optional<FileFull.Map> mapTo(String pkg, Map<String,String> map, String out){
    return map.keySet().stream().filter(k -> map.get(k).equals(out)).findFirst().map(k -> new FileFull.Map(k, out, pkg, List.of()));
  }
  public static List<String> visible(String pkg, Map<String,String> map, Collection<TName> other){
    return other.stream().map(TName::pkgName)
      .map(p -> mapTo(pkg, map, p).map(FileFull.Map::in).orElse(p))
      .distinct().sorted().toList();
  }
  public static String nameOf(String pkg, Map<String,String> map, TName t){
    var alias= map.keySet().stream().filter(k -> map.get(k).equals(t.s())).findFirst();
    if (alias.isPresent()){ return alias.get(); }
    if (t.pkgName().equals(pkg)){ return t.simpleName(); }
    return mapTo(pkg, map, t.pkgName()).map(FileFull.Map::in).orElse(t.pkgName())+"."+t.simpleName();
  }
  public record Logger(boolean active, ArrayList<String> logs){
    public void logInferenceDeclaration(E.Literal d, List<T.C> cs){
      if (!active){ return; }
      logs.add(d.name().s()+Join.of(d.bs(), "[", ", ", "]", "")+":"+Join.of(cs, "", ", ", "", "")+"{'"+d.thisName()+Join.of(d.ms(), "", "", "", "")+"}");
    }
  }
}