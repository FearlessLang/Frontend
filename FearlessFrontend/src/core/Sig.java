package core;

import static offensiveUtils.Require.*;

import java.util.List;

import utils.Join;

public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, TName origin, boolean abs, TSpan span){
  public String toString(){ return " "+rc.toStrSpace()+m+Join.of(bs,"[",",","]","")+Join.of(ts,"(",",",")","")+":"+ret+"@"+origin.s()+";"; }
  public Sig implementedBy(TName name){ return new Sig(rc,m,bs,ts,ret,name,false,span); }
  public Sig{
    assert nonNull(rc,m,ret,origin);
    assert unmodifiableDistinct(bs,"Sig.bs");
    assert unmodifiable(ts,"Sig.ts");
  }
}