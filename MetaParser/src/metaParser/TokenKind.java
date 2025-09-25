package metaParser;

public interface TokenKind{
  TokenMatch matcher();
  int priority();
  boolean hidden();
}