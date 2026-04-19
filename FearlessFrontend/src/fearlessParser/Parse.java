package fearlessParser;

import static fearlessParser.TokenKind.*;

import java.net.URI;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import fearlessFullGrammar.FileFull;
import message.BadTokens;
import message.FearlessErrFactory;
import metaParser.TokenTreeSpec;
import tools.Fs;

public class Parse {
  public static final List<TokenKind> kinds= Stream.of(TokenKind.values()).filter(t->!t.syntetic()).toList();
  private static final TokenTreeSpec<Token,TokenKind> map= new TokenTreeSpec<Token,TokenKind>()
    .addOpenClose(_SOF,_EOF,_All)
    .addOpenClose(ORound,CRound,_RoundGroup)
    .addOpenClose(OSquareArg,CSquare,_SquareGroup)
    .addOpenClose(OCurly,CCurly,_CurlyGroup)
    .addOpenClose(OCurly,CCurlyId,_CurlyGroup)
    
    .addBarriers(ORound,Set.of(SemiColon,Arrow,SQuote))
    .addBarriers(OSquareArg,Set.of(SemiColon,Arrow,SQuote,LowercaseId,ORound,OCurly,DotName))
    
    .addCloserEater(CRound,t->splitOn(t,")",true))
    .addCloserEater(CSquare,t->splitOn(t,"]",true))
    .addCloserEater(CCurly,t->splitOn(t,"}",true))
    .addCloserEater(CCurlyId,t->splitOn(t,"}",true))
    
    .addOpenerEater(ORound,t->splitOn(t,"(",false))
    .addOpenerEater(OSquareArg,t->splitOn(t,"[",false))
    .addOpenerEater(OCurly,t->splitOn(t,"{",false))
    ;
  private static Optional<Token> splitOn(Token t, String s,boolean first){
    var free= t.is(BlockComment, LineComment, UStr, SStr);
    if (!free){ return Optional.empty(); }
    int index= t.content().indexOf(s);
    if (index == -1){ return Optional.empty(); }
    if (first){ return Optional.of(t.tokenFirstHalf(index+1)); }
    return Optional.of(t.tokenSecondHalf(index));
  }
  public static FileFull from(URI fileName,String input){
    Tokenizer t= new Tokenizer()
      .input(fileName,input)
      .tokenKinds(kinds,_SOF,_EOF)
      .startingPosition(1,1)
      .setErrFactory(new FearlessErrFactory())
      .whiteList(Fs.allowed)
      .tokenize()
      .postTokenize(new BadTokens().badTokensMap())
      .buildTokenTree(map);
    var p= new Parser(t.span(),new Names(List.of(),List.of(),List.of()),t.tokenTree(),new FearlessErrFactory());
    return p.parseAll("full file",Parser::parseFileFull);
  }
}