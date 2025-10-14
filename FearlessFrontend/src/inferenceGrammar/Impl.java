package inferenceGrammar;

import java.util.List;
import java.util.Optional;

import fearlessFullGrammar.MName;

public record Impl(Optional<MName> m, List<String> xs, E e){}