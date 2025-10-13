package fearlessParser;

import java.util.Collections;
import java.util.List;

import utils.Push;

record Names(List<String> xs, List<String> Xs, List<String> notFunneled){
  Names{ 
    assert xs.stream().allMatch(s->TokenKind.validate(s,"parameter name", TokenKind.LowercaseId));
    assert Xs.stream().allMatch(s->TokenKind.validate(s,"generic type name", TokenKind.UppercaseId));
  }
  boolean xIn(String x){ return xs.contains(x); }
  boolean XIn(String X){ return Xs.contains(X); }
  Names add(List<String> xs, List<String> Xs){
    assert compatible(xs,Xs);
    return new Names(Push.of(this.xs,xs),Push.of(this.Xs,Xs),notFunneled);
  }
  Names addXs(List<String> Xs){
    assert compatible(List.of(),Xs);
    return new Names(this.xs,Push.of(this.Xs,Xs),notFunneled);
  }
  Names setFunnelledXs(List<String> FXs){
    assert Xs.containsAll(FXs);
    List<String> not= Xs.stream().filter(X->!FXs.contains(X)).toList();
    return new Names(xs,Xs,not);
  }
  boolean compatible(List<String> xs, List<String> Xs){
    return xs.stream().distinct().count() == (long)xs.size()
      &&   Xs.stream().distinct().count() == (long)Xs.size()
      &&   Collections.disjoint(xs, this.xs())
      &&   Collections.disjoint(Xs, this.Xs());
  }
}