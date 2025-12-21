package typeSystem;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import core.*;
import core.E.*;
import utils.Bug;

public sealed interface TypeScope{
  static TypeScope top(){ return Top.Instance; }
  TypeScope outer();
  default boolean isTop(){ return this instanceof Top; }
  E contextE();
  List<T> mentionedTs();
  default TypeScope pushMethod(Literal l, M m){ return new Method(l,m,this); }
  default TypeScope pushCall(Call c){ return new CallSite(c,this); }
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
    var es= IntStream.range(0, c.es().size()).mapToObj(j->j==i?c.es().get(j):omit(c.es().get(j))).toList();
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
  static void walk(T decl, T req, List<T> out){
    switch (decl){
      case T.X _ -> out.add(req);
      case T.RCX _ -> out.add(req);
      case T.ReadImmX _ -> out.add(req);
      case T.RCC drcc -> {//If the types do not match, just skip the rest here (user error too hard to grasp)
        if (!(req instanceof T.RCC rcc)
         || rcc.rc() != drcc.rc() 
         || !rcc.c().name().equals(drcc.c().name())
         || rcc.c().ts().size() != drcc.c().ts().size()
         ){ return; } 
        IntStream.range(0,rcc.c().ts().size())
          .forEach(i->walk(drcc.c().ts().get(i), rcc.c().ts().get(i), out));
      }
    }
  }
  static TypeScope bestInterestingScope(TypeScope start, T declRet, T reqRet){
    var interest= interestFromDeclVsReq(declRet, reqRet);
    if (interest.isEmpty()){ return start; }
    return bestInterestingScope(start, interest);
  }
  static TypeScope bestInterestingScope(TypeScope start, List<T> interest){
    int gapLimit= 10;
    int min= 4;
    TypeScope best= start;
    int gaps= gapLimit;
    for(TypeScope it= start; !it.isTop(); it = it.outer()){
      if (min --> 0 || mentionsAny(it, interest)){ best= it; gaps= gapLimit; continue; }
      if (gaps --> gapLimit){ return best; }
    }
    return best;
  }
  static boolean mentionsAny(TypeScope s, List<T> interest){
    return s.mentionedTs().stream().anyMatch(mt ->
      interest.stream().anyMatch(it -> eqForHeuristic(mt, it))
    );
  }
  static boolean eqForHeuristic(T a, T b){
    return switch(a){
      case T.X _ -> a.equals(b);
      case T.ReadImmX ax -> (b instanceof T.ReadImmX bx) && ax.x().equals(bx.x());
      case T.RCX ar -> (b instanceof T.RCX br) && ar.x().equals(br.x());
      case T.RCC ar -> (b instanceof T.RCC br) && ar.c().equals(br.c());
    };
  }
}