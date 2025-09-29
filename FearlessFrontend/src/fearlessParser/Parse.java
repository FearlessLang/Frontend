package fearlessParser;

import static fearlessParser.TokenKind.*;

import java.net.URI;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

public class Parse {
  public static final List<TokenKind> kinds= Stream.of(TokenKind.values()).filter(t->!t.ignored()).toList();
  public static final Map<TokenKind,Map<TokenKind,TokenKind>> map= Map.of(
      _SOF,Map.of(_EOF,_All),
      ORound,Map.of(CRound,_RoundGroup),
      OSquareArg,Map.of(CSquare,_SquareGroup),
      OCurly,Map.of(CCurly,  _CurlyGroup,
                    CCurlyId,_CurlyGroup));
  public static FileFull from(URI fileName,String input){
    input= input.replace("\r\n", "\n").replace("\r", "\n");
    if (!input.isEmpty() && input.charAt(0) == '\uFEFF'){ input = input.substring(1); }
    new Validate().of(input);
    var t= new Tokenizer(fileName,input,kinds, _SOF, _EOF);
    var all= t.tokenize(map,1,1);
    var p= new Parser(all.span(),new Names(List.of(),List.of()),all.tokenTree());
    return p.parseAll("full file",Parser::parseFileFull);
  }
  static E from(URI fileName, Names names,String input, int line, int col){
    var t= new Tokenizer(fileName,input,kinds, _SOF, _EOF);
    var all= t.tokenize(map,line,col);
    var p= new Parser(all.span(),names,all.tokenTree());
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
  static class Validate{
    int line = 1; int col = 1;
    void of(String src){ src.codePoints().forEach(this::ofSingle); }
    void ofSingle(int cp){
      boolean ok= allowed.indexOf(cp) >= 0;
      if (!ok){
        var err= "Illegal character " + String.format("U+%04X", cp) + " at line=" + line + ", col=" + col;
        throw new IllegalArgumentException(err);
      }
      if (cp == '\n'){ line++; col = 1; } else { col++; }
    }
  }
}