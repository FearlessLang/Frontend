package fearlessParser;

import java.util.List;

import utils.Bug;

public class Tokenizer extends metaParser.MetaTokenizer<Token,TokenKind>{

  public Tokenizer(List<TokenKind> tks, TokenKind sof, TokenKind eof) {
    super(tks, sof, eof);
  }
  @Override public Token make(TokenKind kind, String text, int line, int col, List<Token> tokens){
    return new Token(kind,text,line,col,tokens);
  }
  @Override public List<Token> tokenize(String i){
    var res= super.tokenize(i);
    res.stream().forEach(t->{
      if(!t.kind().bad()){ return; }
      throw Bug.of("better error for bad token "+t);
    });
    return res;
  }

}
