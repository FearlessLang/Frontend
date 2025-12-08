package typeSystem;

import static offensiveUtils.Require.nonNull;

import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import core.*;
import core.E.*;

public sealed interface Change{
  Optional<T> view();
  Why why();
  Change map(Function<T,Change> f);
  static Change drop(Why why){ return new Drop(why); }
  static Change keep(T in, T out, Why why){ return out.equals(in) ? new Same(out) : new Keep(out, why); }
  public record Same(T t) implements Change{
    public Same{ assert nonNull(t); }
    public Optional<T> view(){ return Optional.of(t); }
    public Why why(){ return (_,_,_,_,_)->""; }
    public Change map(Function<T,Change> f){ return f.apply(t); }
  }
  public record Keep(T t, Why why) implements Change{
    public Keep{ assert nonNull(t,why); }
    public Optional<T> view(){ return Optional.of(t); }
    public Change map(Function<T,Change> f){ return merge(f.apply(t)); }
    private Change merge(Change next){ return switch(next){
      case Same _->this;
      case Keep k -> new Keep(k.t(), why.then(next.why()));
      case Drop _->next;
    };}
  }
  public interface Why{
    String render(String x, T expected, Optional<T> got, T declared, List<B> bs);
    default Why then(Why next){
      return (x, expected, got, declared, bs)->{
        String a= render(x, expected, got, declared, bs);
        String b= next.render(x, expected, got, declared, bs);
        if (a.isEmpty()){ return b; }
        if (b.isEmpty()){ return a; }
        return a+"\n"+b;//TODO: later this may change in some other kind of formatting
      };
    }
  }
  public record Drop(Why why) implements Change{
    public Drop{ assert nonNull(why); }
    public Optional<T> view(){ return Optional.empty(); }
    public Change map(Function<T,Change> f){ return this; }
  }
}