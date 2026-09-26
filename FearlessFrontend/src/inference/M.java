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
    return impl.map(i->sig+Join.of(i.xs,"(",", ",")","")+"->"+i.e()+";").orElseGet(sig::toString);
    }
  public M withSig(Sig sig){
    if (sig.equals(this.sig)){ return this; }
    return new M(sig,impl);
    }
  public record Sig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Optional<IT>> ts, Optional<IT> ret, Optional<TName> origin, boolean abs, TSpan span){
    public Sig{ assert nonNull(rc,m,bs,ts,ret,origin); assert validOpt(bs,_bs->unmodifiableDistinct(_bs,"bounds")); assert unmodifiable(ts,"Sig.ts"); }
    public Sig(RC rc, MName m, List<B> bs, List<Optional<IT>> ts, IT ret, TName origin, boolean abs, TSpan span){
      this(Optional.of(rc),Optional.of(m),Optional.of(bs),ts,Optional.of(ret),Optional.of(origin),abs,span);
    }
    public String toString(){
      var bsS= bs.map(b->Join.of(b,"[",",","]","")).orElse("[?]");
      return " "+rc.map(RC::toStrSpace).orElse("? ")+m.map(MName::toString).orElse("")+bsS
        +Join.of(ts.stream().map(this::t),"(",",",")","")+":"+t(ret)+origin.map(o->"@"+o.s()).orElse("@!")+";";
    }    
    private String t(Optional<IT> ot){ return ot.map(Object::toString).orElse("?"); }
    public Sig withTsT(List<Optional<IT>> ts, IT ret){
      if (ts.equals(this.ts) && this.ret.equals(Optional.of(ret))){ return this; }
      return new Sig(rc,m,bs,ts,Optional.of(ret),origin,abs,span);
    }
    public Sig withOrigin(TName origin){
      return new Sig(rc,m,bs,ts,ret,Optional.of(origin),abs,span);
    }
    public boolean isFull(){ return rc.isPresent() && m.isPresent() && bs.isPresent() && ts.stream().allMatch(Optional::isPresent) && ret.isPresent(); }
  }
  public record Impl(Optional<MName> m, List<String> xs, E e){
    public Impl{ assert nonNull(m,e); assert unmodifiable(xs,"Impl.xs"); }
    public String toString(){
      var xsC= Join.of(xs,"(",", ",")->","()->");
      return " "+m.map(MName::s).orElse("")+xsC+e+";";
    }
    public Impl withE(E e){
      assert e == this.e || !e.equals(this.e);
      if (e == this.e){ return this; }
      return new Impl(m,xs,e);
    }
  }
}