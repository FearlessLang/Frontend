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
import utils.OneOr;

public record Package(String name, Map<String,String> map, Map<String,String> writtenIn, List<FileFull.Use> uses, List<Declaration> decs, DeclaredNames names, Logger log){
  public WellFormednessErrors err(){ return new WellFormednessErrors(name, map, writtenIn, new LinkedHashSet<>()); }
  public static Optional<String> mapTo(Map<String,String> map, String out){
    return OneOr.opt("two names for "+out, map.keySet().stream().filter(k -> map.get(k).equals(out)));
  }
  public static String writtenPkg(Map<String,String> map, String pkg){ return mapTo(map, pkg).orElse(pkg); }
  public static List<String> visible(Map<String,String> map, Collection<TName> other){
    return other.stream().map(t -> writtenPkg(map, t.pkgName())).distinct().sorted().toList();
  }
  public static String nameOf(String pkg, Map<String,String> map, TName t){
    if (t.pkgName().equals(pkg)){ return t.simpleName(); }
    return mapTo(map, t.s()).orElseGet(() -> writtenPkg(map, t.pkgName())+"."+t.simpleName());
  }
  public record Logger(boolean active, ArrayList<String> logs){
    public void logInferenceDeclaration(E.Literal d, List<T.C> cs){
      if (!active){ return; }
      logs.add(d.name().s()+Join.of(d.bs(), "[", ", ", "]", "")+":"+Join.of(cs, "", ", ", "", "")+"{'"+d.thisName()+Join.of(d.ms(), "", "", "", "")+"}");
    }
  }
}