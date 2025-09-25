package metaParser;

import java.util.stream.Collectors;

public class PrettyToken{
  private PrettyToken(){}
  public static String showText(String s){
    s = s.replace("\n","\\n").replace("\r","\\r").replace("\t","\\t");
    return s.length()<=24 ? s : s.substring(0,21)+"...";
  }
  public static <T extends Token<T,TK>, TK extends TokenKind> String show(T t){
    return t.kind()+" `"+showText(t.content())+"` @"+t.line()+":"+t.column()
      + t.tokens().stream().map(ti->show(ti)).collect(Collectors.joining());
    //can we use a more 'unusual but still ashii' character instead of `,' or " to mark start/end?
  }
}