package metaParser;

import java.util.stream.Stream;

public interface TokenProcessor<
    T extends Token<T,TK>,
    TK extends TokenKind,
    E extends RuntimeException & HasFrames<E>,
    Tokenizer extends MetaTokenizer<T,TK,E,Tokenizer,Parser,Err>,
    Parser extends MetaParser<T,TK,E,Tokenizer,Parser,Err>,
    Err extends ErrFactory<T,TK,E,Tokenizer,Parser,Err>
  > {
  Stream<T> process(int index, T token, Tokenizer tokenizer);
}
