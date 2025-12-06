package core;

import fearlessFullGrammar.E;
import files.Pos;
import offensiveUtils.EqTransparent;
import offensiveUtils.NeverAsKey;

/** Never as Map/Set key (nondiscriminating equals/hashCode). Build-time checker rejects it. */
@NeverAsKey
public class Src extends EqTransparent<E>{
  public static Src syntetic=new Src(new fearlessFullGrammar.E.X("this",Pos.UNKNOWN));
  public Src(E inner){ super(inner); }
}
