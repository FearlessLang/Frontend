package fullWellFormedness;

import java.net.URI;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull;
import fearlessFullGrammar.FileFull.Role;
import fearlessFullGrammar.TName;
import fearlessParser.Parse;
import message.SourceOracle;
import utils.Bug;
import static offensiveUtils.Require.*;
import static fearlessParser.TokenKind.*;

public class ParsePackage {
  Package of(List<FileFull.Map> override, List<URI> files, SourceOracle o){
    Map<URI,FileFull> all= new LinkedHashMap<>();
    for(var u : files){
      var str= o.loadString(u);
      var f= Parse.from(u, str);
      all.put(u, f);
    }
    return merge(override,all);
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
    if (head.role().isEmpty()){ WellFormednessErrors.noRole(headPkg,head ); }
    var res= new Package(head.name(),head.role().get(),ds);
    var uses = new HashMap<TName,String>();
    for (var u: head.uses()){ uses.put(u.in(),u.out()); }
    res = applyUses(res,uses);
    var map = new HashMap<String,String>();
    for (var m: head.maps()){ map.put(m.in(),m.out()); }
    for (var m: override){ map.put(m.in(),m.out()); }
    res = applyMap(res,map);
    wellFormed(res);
    return res;
  }
  Package applyMap(Package p,Map<String,String> map){ throw Bug.todo(); }
  Package applyUses(Package p, Map<TName,String> uses){ throw Bug.todo(); }
  URI afterPackage(String pkgName, Set<URI> uris){
    assert nonNull(uris);
    assert validate("",pkgName,_pkgName);
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
  boolean wellFormed(Package p){ throw Bug.todo(); }
}
record Package(String name, Role role, List<Declaration> decs){}