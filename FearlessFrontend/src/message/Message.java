package message;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public record Message(String msg,int priority){
  public static final SnippetFormatter base= SnippetFormatter.builder()
      .maxMiddleLines(5)
      .contextBefore(4)
      .contextAfter(4)
      .showLineNumbers(true)
      .tabWidth(4)
      .build();
  public static List<Message> of(SourceOracle o, List<Frame> fs, String msg){
    return allMessages(new Message(msg,1),o,fs);
  }
  private static List<Message> allMessages(Message m, SourceOracle o, List<Frame> fs){
    var out= new ArrayList<Message>(fs.size()+1);
    for (int i= 0; i < fs.size(); i++){
      Frame f= fs.get(i);
      Span s= f.s().get();
      int pr= 10 + i;
      String body= "While inspecting " +f.name()+"\n"+ 
        base.caret(()->o.loadString(s.fileName()),s);
      if (i == 0) { body = "In file: "+PrettyFileName.displayFileName(s.fileName()) +"\n"+ body; }
      out.add(new Message(body, pr));
    }
    out.add(1,m);//leave the first caret as the most informative source of help
    return Collections.unmodifiableList(out);
  }
}