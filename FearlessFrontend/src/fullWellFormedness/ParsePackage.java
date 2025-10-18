package fullWellFormedness;

import java.net.URI;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.FileFull.Role;
import fearlessParser.Parse;
import message.SourceOracle;
import static offensiveUtils.Require.*;
import static fearlessParser.TokenKind.*;

public class ParsePackage{
  public List<inferenceGrammar.Declaration> of(List<FileFull.Map> override, List<URI> files, SourceOracle o, int steps){
    Map<URI,FileFull> all= new LinkedHashMap<>();
    for(var u : files){
      var str= o.loadString(u);
      var f= Parse.from(u, str);
      all.put(u, f);
    }
    return infer(merge(override,all),steps);
  }
  Package merge(List<FileFull.Map> override, Map<URI,FileFull> all){
    String pkgName= all.values().iterator().next().name();
    assert all.values().stream().allMatch(f->f.name().equals(pkgName));
    URI headPkg= afterPackage(pkgName,all.keySet());
    all.entrySet().stream().filter(e->e.getKey() != headPkg)
      .filter(e->!(e.getValue().maps().isEmpty() && e.getValue().uses().isEmpty() && e.getValue().role().isEmpty()))
      .forEach(e->{ throw WellFormednessErrors.notClean(e.getKey(),e.getValue()); });
    List<Declaration> ds= all.values().stream().flatMap(f->f.decs().stream()).toList();
    var head= all.get(headPkg);
    if (head.role().isEmpty()){ throw WellFormednessErrors.noRole(headPkg,head ); }
    var map= new HashMap<String,String>();
    acc(pkgName,map,head.maps());
    acc(pkgName,map,override);
    accUse(pkgName,map,head.uses());
    var names= DeclaredNames.of(pkgName,ds,Collections.unmodifiableMap(map));
    return new Package(pkgName,head.role().get(),map,ds,names);
  }
  List<inferenceGrammar.Declaration> infer(Package p, int steps){
    var iDecs= new ToInference().of(p,p.map());
    return iDecs;//TODO: (later) inference here using 'steps
  }
  void acc(String n, HashMap<String,String> map, List<FileFull.Map> maps){
    for (var m: maps){ if (n.equals(m.target())){ map.put(m.out(),m.in()); } }
    //map a as b in c //inside c, replace b with a
  }
  void accUse(String n, HashMap<String,String> map, List<FileFull.Use> uses){
    for (var u: uses){
      var p= u.in().pkgName();
      p = map.getOrDefault(p,p);//if "" will return "" anyway
      map.put(u.out(),p+"."+u.in().simpleName());
    }
    //map a as b in c
    //use b.F as bF // replace bF with a.F
  }
  URI afterPackage(String pkgName, Set<URI> uris){
    assert nonNull(uris);
    assert validate(pkgName,"",_pkgName);
    var heads= uris.stream().filter(u->{
      assert u != null && !u.isOpaque();
      String path= u.getPath();
      assert path != null && !path.isEmpty();
      int slash= path.lastIndexOf('/');
      String name= slash >= 0 ? path.substring(slash + 1) : path;
      assert !name.isEmpty();
      int dot= name.lastIndexOf('.');
      assert dot > 0 && dot < name.length() - 1;
      String base= name.substring(0,dot);
      return base.equals(pkgName);
      }).toList();
    if (heads.size() == 1){ return heads.getFirst(); }
    throw WellFormednessErrors.expectedSingleUriForPackage(heads,pkgName);
  }
}
record Package(String name, Role role, HashMap<String,String> map, List<Declaration> decs, DeclaredNames names){}