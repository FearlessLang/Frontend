package inferenceGrammar;

import java.util.List;

import fearlessFullGrammar.MName;
import fearlessParser.RC;
import files.Pos;

public record Sig(RC rc, MName m, List<B> bs, List<T> ts, T ret, Pos pos){}