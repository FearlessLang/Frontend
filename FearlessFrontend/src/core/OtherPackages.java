package core;

import java.util.Collection;
import java.util.List;

public interface OtherPackages{
  core.E.Literal of(TName name);
  Collection<TName> dom();
  static OtherPackages empty(){ return new OtherPackages(){
    public core.E.Literal of(TName name){ return null; }
    public Collection<TName> dom(){ return List.of(); }
  };}
}