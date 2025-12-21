package inference;
import java.util.List;
import java.util.Optional;

import core.B;
import core.MName;
import core.RC;
import core.TName;
import core.TSpan;
import utils.Join;

import static offensiveUtils.Require.*;

public record M(Sig sig, Optional<Impl> impl){
  public M{ assert nonNull(sig,impl); }
  public String toString(){
    if (impl.isEmpty()){ return sig.toString();}
    var xs=impl.get().xs;
    var args= Join.of(xs,"(",", ",")","");
    return sig + args+ "->"+impl.get().e()+";";
    }
  public M withSig(Sig sig){ return new M(sig,impl); }
  public record Sig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Optional<IT>> ts, Optional<IT> ret, Optional<TName> origin, boolean abs, TSpan span){
    public Sig{ assert nonNull(rc,m,bs,ts,ret,origin); assert validOpt(bs,_bs->unmodifiableDistinct(_bs,"bounds")); }
    public Sig(RC rc, MName m, List<B> bs, List<Optional<IT>> ts, IT ret, TName origin, boolean abs, TSpan span){
      this(Optional.of(rc),Optional.of(m),Optional.of(bs),ts,Optional.of(ret),Optional.of(origin),abs,span);
    }
    public String toString(){
      var bsS= bs.isEmpty() ? "[?]" : Join.of(bs.get(),"[",",","]","");
      var tsS= Join.of(ts.stream().map(this::t),"(",",",")","");
      var rcS= rc.map(RC::toStrSpace).orElse("? ");
      var ori= origin.map(o->"@"+o.s()).orElse("@!");
      var mS= m.isPresent()?m.get().toString():"";
      return " "+rcS+mS+bsS+tsS+":"+t(ret)+ori+";";
    }    
    private String t(Optional<IT> ot){ return ot.map(Object::toString).orElse("?"); }
    public Sig withTsT(List<Optional<IT>> ts, IT ret){
      if (ts.equals(this.ts) && this.ret.isPresent() && this.ret.get().equals(ret)){ return this; }
      return new Sig(rc,m,bs,ts,Optional.of(ret),origin,abs,span);
    }
    public Sig withBsTsT(List<B> bs, List<Optional<IT>> ts, IT ret){
      if (this.bs.isPresent() && bs.equals(this.bs.get()) && ts.equals(this.ts) && this.ret.isPresent() && this.ret.get().equals(ret)){ return this; } 
      return new Sig(rc,m,Optional.of(bs),ts,Optional.of(ret),origin,abs,span); 
    }
    public Sig withOrigin(TName origin){
      return new Sig(rc,m,bs,ts,ret,Optional.of(origin),abs,span);
    }
    public boolean isFull(){ return rc.isPresent() && m.isPresent() && bs.isPresent() && ts.stream().allMatch(Optional::isPresent) && ret.isPresent(); }
  }
  public record Impl(Optional<MName> m, List<String> xs, E e){
    public String toString(){
      var xsC= Join.of(xs,"(",", ",")->","()->");
      return " "+m.map(n->n.s()).orElse("")+xsC+e+";";
    }
    public Impl withE(E e){
      if (e == this.e){ return this; }
      return new Impl(m,xs,e);
    }
  }
}