package pkgmerge;

import java.util.Collection;

import fearlessFullGrammar.TName;
import inferenceCore.Declaration;

public interface OtherPackages{
  Declaration of(TName name);
  Collection<TName> dom();
}