package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

import java.util.List;
import core.TName;
import utils.Join;

public record FileFull(
  List<Map> maps,
  List<Use> uses,
  List<Declaration> decs
  ){
  public FileFull{
    assert unmodifiableDistinct(uses, "FileFull.uses");
    assert unmodifiableDistinct(maps, "FileFull.maps");
    assert unmodifiableDistinct(decs, "FileFull.decs");
  }
  public record Use(TName in, String out){
    public Use{ assert nonNull(in, out); assert validate(out, "Use.out", _XId); }
    @Override public String toString(){ return "use "+in.s()+" as "+out; }
  }
  public record Map(String in, String out, String target, List<String> insteadOf){
    public Map{
      assert validate(in, "map.in", _pkgName);
      assert validate(out, "map.out", _pkgName);
      assert validate(target, "map.target", _pkgName);
      assert insteadOf.stream().allMatch(o -> validate(o, "map.insteadOf", _pkgName));
    }
    @Override public String toString(){ return "map "+in+" as _"+out+" in _"+target+Join.of(insteadOf.stream().map(o -> "_"+o), " instead of ", ", ", "", ""); }
  }
  public boolean noDirectives(){ return maps.isEmpty() && uses.isEmpty(); }
}