package pkgmerge;

import java.util.Collection;

import fearlessFullGrammar.TName;

public interface OtherPackages{
  core.E.Literal of(TName name);
  Collection<TName> dom();
}