package typeSystem;

import java.util.List;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.*;
import core.E.*;
import utils.Bug;
import utils.Streams;

public sealed interface TypeScope{
  static TypeScope top(){ return Top.Instance; }
  TypeScope outer();
  default Stream<TypeScope> scopes(){ return Stream.iterate(this, s -> !(s instanceof Top), TypeScope::outer); }
  default Stream<Method> methods(){ return scopes().filter(Method.class::isInstance).map(Method.class::cast); }
  E contextE();
  List<T> mentionedTs();
  enum Top implements TypeScope{
    Instance;
    @Override public List<T> mentionedTs(){ throw Bug.unreachable(); }
    @Override public TypeScope outer(){ throw Bug.unreachable(); }//consistently offensive
    @Override public E contextE(){ throw Bug.unreachable(); }
  }
  default TypeScope pushM(Literal l, M m){ return new Method(l, m, this); }
  record Method(Literal l, M m, TypeScope outer) implements TypeScope{
    @Override public E contextE(){ return l; }
    @Override public List<T> mentionedTs(){ return l.cs().stream().flatMap(c -> c.ts().stream()).toList(); }
  }
  default TypeScope pushCall(Call c){ return new CallSite(c, this); }
  record CallSite(Call c, TypeScope outer) implements TypeScope{
    @Override public E contextE(){ return c; }
    @Override public List<T> mentionedTs(){ return c.targs(); }
  }
  static List<T> interestFromDeclVsReq(T declRet, T reqRet){ return walk(declRet, reqRet).toList(); }
  static Stream<T> walk(T decl, T req){
    if (!(decl instanceof T.RCC(var declRc, var declC, _))){ return Stream.of(req); }
    //If the types do not match, just skip the rest here (user error too hard to grasp)
    if (!(req instanceof T.RCC(var reqRc, var reqC, _))){ return Stream.of(); }
    var sameShape= reqRc == declRc && reqC.name().equals(declC.name());
    if (!sameShape){ return Stream.of(); }
    return Streams.zip(declC.ts(), reqC.ts()).flatMap(TypeScope::walk);
  }
  static TypeScope bestInterestingScope(TypeScope start, List<T> interest){
    var ss= start.scopes().toList();
    return ss.get(IntStream.range(0, ss.size()).filter(i -> i < 4 || mentionsAny(ss.get(i), interest)).max().getAsInt());
  }
  static boolean mentionsAny(TypeScope s, List<T> interest){
    return s.mentionedTs().stream().anyMatch(mt ->
      interest.stream().anyMatch(it -> eqForHeuristic(mt, it))
    );
  }
  static boolean eqForHeuristic(T a, T b){ return a.getClass() == b.getClass() && a.withRC(RC.imm).equals(b.withRC(RC.imm)); }
}