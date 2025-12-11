package core;

import fearlessFullGrammar.E;
import fearlessFullGrammar.TSpan;
import files.Pos;
import offensiveUtils.EqTransparent;
import offensiveUtils.NeverAsKey;

/** Never as Map/Set key (nondiscriminating equals/hashCode). Build-time checker rejects it. */
@NeverAsKey
public class Src extends EqTransparent<core.Src.SrcObj>{
  public interface SrcObj{ Pos pos(); TSpan span(); }
  public static Src syntetic=new Src(new fearlessFullGrammar.E.X("this",Pos.UNKNOWN));
  public Src(SrcObj inner){ super(inner); }
}
