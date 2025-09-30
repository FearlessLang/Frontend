package fearlessParser;

import java.net.URI;
import java.util.List;

import message.FearlessErrFactory;
import message.FearlessException;
import metaParser.MetaTokenizer;
import metaParser.Span;

public class Tokenizer extends MetaTokenizer<Token,TokenKind,FearlessException>{

  public Tokenizer(URI fileName, String input, List<TokenKind> tks, TokenKind sof, TokenKind eof) {
    super(fileName,input,tks, sof, eof);
  }
  @Override public Token make(TokenKind kind, String text, int line, int col, List<Token> tokens){
    return new Token(kind,text,line,col,tokens);
  }
  @Override public List<Token> tokenize(int line, int col){
    var res= super.tokenize(line, col);
    res.stream().forEach(t->{
      if(!t.kind().bad()){ return; }
      throw errFactory().badTokenAt(new Span(fileName(),t.line(),t.column(),t.line(),t.column()),t.kind(),t.content());
    });
    return res;
  }
  @Override public FearlessErrFactory errFactory(){
    return new FearlessErrFactory();
  }

}
