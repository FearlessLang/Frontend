package fearlessParser;

import static fearlessParser.TokenKind.*;

import java.net.URI;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import message.BadTokens;
import message.FearlessErrFactory;
import metaParser.MetaParser;
import metaParser.Span;
import metaParser.TokenTreeSpec;

public class Parse {
  public static final List<TokenKind> kinds= Stream.of(TokenKind.values()).filter(t->!t.syntetic()).toList();
  private static final TokenTreeSpec<Token,TokenKind> map= new TokenTreeSpec<Token,TokenKind>()
    .addOpenClose(_SOF,_EOF,_All)
    .addOpenClose(ORound,CRound,_RoundGroup)
    .addOpenClose(OSquareArg,CSquare,_SquareGroup)
    .addOpenClose(OCurly,CCurly,_CurlyGroup)
    .addOpenClose(OCurly,CCurlyId,_CurlyGroup)
    
    .addBarriers(ORound,Set.of(SemiColon,Arrow,BackTick))
    .addBarriers(OSquareArg,Set.of(SemiColon,Arrow,BackTick,LowercaseId,ORound,OCurly,DotName))
    
    .addCloserEater(CRound,t->splitOn(t,")",true))
    .addCloserEater(CSquare,t->splitOn(t,"]",true))
    .addCloserEater(CCurly,t->splitOn(t,"}",true))
    .addCloserEater(CCurlyId,t->splitOn(t,"}",true))
    
    .addOpenerEater(ORound,t->splitOn(t,"(",false))
    .addOpenerEater(OSquareArg,t->splitOn(t,"[",false))
    .addOpenerEater(OCurly,t->splitOn(t,"{",false))
    ;
  private static Optional<Token> splitOn(Token t, String s,boolean first){
    var free= t.is(BlockComment, LineComment, UStr, SStr, UStrLine, SStrLine, UStrInterHash, SStrInterHash);
    if(!free){ return Optional.empty(); }
    int index= t.content().indexOf(s);
    if (index == -1){ return Optional.empty(); }
    if(first){ return Optional.of(t.tokenFirstHalf(index+1)); }
    return Optional.of(t.tokenSecondHalf(index));
  }
  public static FileFull from(URI fileName,String input){
    Tokenizer t= new Tokenizer()
      .input(fileName,input)
      .tokenKinds(kinds,_SOF,_EOF)
      .startingPosition(1,1)
      .setErrFactory(new FearlessErrFactory())
      .whiteList(allowed)
      .tokenize()
      .postTokenize(new BadTokens().badTokensMap())
      .buildTokenTree(map);
    var p= new Parser(t.span(),new Names(List.of(),List.of()),t.tokenTree());
    return p.parseAll("full file",Parser::parseFileFull);
  }
  static E from(URI fileName, Names names,String input, int line, int col){
    Span s=new Token(SStrInterHash,input,line,col,List.of()).span(fileName);
    Tokenizer t= MetaParser.computeInFrame("string interpolation expression", s, ()->
      new Tokenizer()
        .input(fileName,input)
        .tokenKinds(kinds,_SOF,_EOF)
        .startingPosition(line,col)
        .setErrFactory(new FearlessErrFactory(){
          @Override public String context(){ return "Interpolation expression ended while parsing a "; }
          })
        //not needed .whiteList(allowed)
        .tokenize()
        .postTokenize(new BadTokens().badTokensMap())
        .buildTokenTree(map));
    var p= new Parser(t.span(),names,t.tokenTree());
    return p.parseAll("string interpolation expression",Parser::parseEFull);
  }
  // ASCII whitelist
  private static final String allowed=
    "0123456789" +
    "abcdefghijklmnopqrstuvwxyz" +
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ" +
    "+-*/=<>,.;:()[]{}" +
    "`'\"!?@#$%^&_|~\\" +
    " \n";
}