package fullWellFormedness;

import java.util.Collection;

import fearlessFullGrammar.TName;
import inferenceGrammarB.Declaration;

public interface OtherPackages{
  Declaration of(TName name);
  Collection<TName> dom();
}