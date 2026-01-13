package fearlessParser;

import java.util.List;

import core.FearlessException;
import message.FearlessErrFactory;
import metaParser.MetaTokenizer;

public class Tokenizer extends MetaTokenizer<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>{
  @Override public Token make(TokenKind kind, String text, int line, int col, List<Token> tokens){
    return new Token(kind,text,line,col,tokens);
  }
  @Override public Tokenizer self(){ return this; }
}
