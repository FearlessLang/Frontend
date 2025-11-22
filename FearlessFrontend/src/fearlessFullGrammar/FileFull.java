package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import java.util.Optional;

public record FileFull(
  String name,
  Optional<Role> role,
  List<Map> maps,
  List<Use> uses,
  List<Declaration> decs
  ){
  public FileFull{
    assert name.isEmpty() || validate(name,"pkgName", _pkgName);
    assert nonNull(role);
    assert unmodifiable(uses, "FileFull.uses");
    assert unmodifiable(maps, "FileFull.maps");
    assert unmodifiable(decs, "FileFull.decs"); 
  }
  public enum RoleName{base,core,driver,worker,framework,accumulator,tool,app}
  public record Role(RoleName role,int index){
    public Role{
      assert index >= 0 && index < 1000: index;
      assert nonNull(role);
      }
    public String toString(){ return "role "+role.name()+index; }
  }
  public record Use(TName in,String out){
    public Use{assert nonNull(in,out); assert validate(out,"Use.out",_XId);}}
  public record Map(String in,String out, String target){ public Map{
    assert validate(in,"map.in", _pkgName);
    assert validate(out,"map.out", _pkgName);
    assert validate(target,"map.target", _pkgName);
  }}
}