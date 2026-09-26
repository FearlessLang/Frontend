package typeSystem;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import utils.Bug;
import utils.Streams;

public sealed interface TypeScope{
  static TypeScope top(){ return Top.Instance; }
  TypeScope outer();
  default boolean isTop(){ return this instanceof Top; }
  E contextE();
  List<T> mentionedTs();
  enum Top implements TypeScope{
    Instance;
    public List<T> mentionedTs(){ return List.of(); }
    public TypeScope outer(){ throw Bug.unreachable(); }//consistently offensive
    public E contextE(){ throw Bug.unreachable(); }
  }
  default TypeScope pushM(Literal l, M m){ return new Method(l,m,this); }
  record Method(Literal l, M m, TypeScope outer) implements TypeScope{
    public E contextE(){ return l; }
    public List<T> mentionedTs(){ return l.cs().stream().flatMap(c->c.ts().stream()).toList(); }
  }
  default TypeScope pushCallRec(Call c){
    var es= c.es().stream().map(this::omit).toList();
    return new CallSite(new Call(c.e(),c.name(),c.rc(),c.targs(),es,c.expectedRes(),c.src()),this);
  }
  default E omit(E e){ return new X("-",e.src()); }
  default TypeScope pushCallArgi(Call c, int i){
    var es= IntStream.range(0, c.es().size()).mapToObj(j->j == i ? c.es().get(j) : omit(c.es().get(j))).toList();
    return new CallSite(new Call(omit(c.e()),c.name(),c.rc(),c.targs(),es,c.expectedRes(),c.src()),this);
  }
  record CallSite(Call c, TypeScope outer) implements TypeScope{
    public E contextE(){ return c; }
    public List<T> mentionedTs(){ return c.targs(); }
  }
  static List<T> interestFromDeclVsReq(T declRet, T reqRet){
    var out= new ArrayList<T>();
    walk(declRet, reqRet, out);
    return out.stream().distinct().toList();
  }
  static void walk(T decl, T req, ArrayList<T> out){
    if (!(decl instanceof T.RCC(var declRc, var declC, _))){ out.add(req); return; }
    //If the types do not match, just skip the rest here (user error too hard to grasp)
    if (!(req instanceof T.RCC(var reqRc, var reqC, _))){ return; }
    var sameShape= reqRc == declRc
      && reqC.name().equals(declC.name())
      && reqC.ts().size() == declC.ts().size();
    if (!sameShape){ return; }
    Streams.zip(declC.ts(), reqC.ts()).forEach((d,r)->walk(d, r, out));
  }
  static TypeScope bestInterestingScope(TypeScope start, List<T> interest){
    var min= 4;
    var best= start;
    for (var it= start; !it.isTop(); it= it.outer()){
      var interesting= min-- > 0 || mentionsAny(it, interest);
      if (interesting){ best= it; }
    }
    return best;
  }
  static boolean mentionsAny(TypeScope s, List<T> interest){
    return s.mentionedTs().stream().anyMatch(mt->
      interest.stream().anyMatch(it->eqForHeuristic(mt, it))
    );
  }
  static boolean eqForHeuristic(T a, T b){
    return switch (a){
      case T.X _ -> a.equals(b);
      case T.ReadImmX(var ax) -> b instanceof T.ReadImmX(var bx) && ax.equals(bx);
      case T.RCX(_, var ax) -> b instanceof T.RCX(_, var bx) && ax.equals(bx);
      case T.RCC(_, var ac, _) -> b instanceof T.RCC(_, var bc, _) && ac.equals(bc);
    };
  }
}