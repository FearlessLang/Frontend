package fearlessParser;

import java.util.Collections;
import java.util.List;

import utils.Push;

record Names(List<String> xs, List<String> Xs){
  Names{ 
    assert xs.stream().allMatch(s->TokenKind.validate(s,"parameter name", TokenKind.LowercaseId));
    assert Xs.stream().allMatch(s->TokenKind.validate(s,"generic type name", TokenKind.UppercaseId));
  }
  boolean xIn(String x){ return xs.contains(x); }
  boolean XIn(String X){ return Xs.contains(X); }
  Names add(List<String> xs, List<String> Xs){
    assert compatible(xs,Xs);
    return new Names(Push.of(this.xs(),xs),Push.of(this.Xs(),Xs));
  }
  Names addXs(List<String> Xs){
    assert compatible(List.of(),Xs);
    return new Names(xs,Push.of(this.Xs(),Xs));
  }
  boolean compatible(List<String> xs, List<String> Xs){
    return xs.stream().distinct().count() == (long)xs.size()
      &&   Xs.stream().distinct().count() == (long)Xs.size()
      &&   Collections.disjoint(xs, this.xs())
      &&   Collections.disjoint(Xs, this.Xs());
  }
}