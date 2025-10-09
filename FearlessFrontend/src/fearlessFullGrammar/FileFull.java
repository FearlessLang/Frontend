package fearlessFullGrammar;

import static offensiveUtils.Require.unmodifiable;

import java.util.List;

public record FileFull(List<Declaration> decs){
  public FileFull{ assert unmodifiable(decs, "FileFull.decs"); }
}