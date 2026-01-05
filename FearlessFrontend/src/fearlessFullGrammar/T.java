package fearlessFullGrammar;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;
import java.util.List;
import java.util.Optional;

import core.RC;
import core.TName;
import core.TSpan;
import inference.IT;

public sealed interface T {
  <R> R accept(TVisitor<R> v);
  TSpan span();
  IT toIT();//TODO: where it is used? why not in TypeRename? or why IT do not have toCore?
  record X(String name, TSpan span) implements T{
    public X{assert validate(name,"generic type name", _XId);}
    public <R> R accept(TVisitor<R> v){ return v.visitTX(this); }
    public IT.X toIT(){ return new IT.X(name,span); }
    public String toString(){ return "X[name="+name+"]";}
  }
  record RCX(RC rc, X x) implements T{
    public RCX{assert nonNull(rc,x);}
    public <R> R accept(TVisitor<R> v){ return v.visitRCX(this); }
    public IT.RCX toIT(){ return new IT.RCX(rc,x.toIT()); }
    public TSpan span(){ return x.span(); }
  }
  record ReadImmX(X x) implements T{
    public ReadImmX{assert nonNull(x);}
    public <R> R accept(TVisitor<R> v){ return v.visitReadImmX(this); }
    public IT.ReadImmX toIT(){ return new IT.ReadImmX(x.toIT()); }
    public TSpan span(){ return x.span(); }
  }
  record C(TName name, Optional<List<T>> ts){
    public C{
      assert validOpt(ts,_ts->{
        unmodifiable(_ts,"T.C.args");
        eq(_ts.size(), name.arity(),"Type arity");
      });
    }
  }
  record RCC(Optional<RC> rc, C c,TSpan span) implements T{
    public RCC{ assert nonNull(rc,c); }
    public <R> R accept(TVisitor<R> v){ return v.visitRCC(this); }
    public IT.RCC toIT(){
      List<IT> ts= c.ts().orElse(List.of()).stream().map(t->t.toIT()).toList();
      return new IT.RCC(rc,new IT.C(c.name(),ts),span); 
    }
    public String toString(){ return "RCC[rc="+rc+",c="+c+"]"; }
  }
}