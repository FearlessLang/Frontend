package inference;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import core.B;
import fearlessFullGrammar.MName;
import fearlessFullGrammar.TName;
import fearlessParser.RC;
import files.Pos;

import static offensiveUtils.Require.*;

public record M(Sig sig, Optional<Impl> impl){
  public M{ assert nonNull(sig,impl); }
  public String toString(){
    if (impl.isEmpty()){ return sig.toString();}
    var xs=impl.get().xs;
    var args= "";
    if (!xs.isEmpty()){ args= "("+xs.stream().collect(Collectors.joining(", "))+")"; }
    return sig + args+ "->"+impl.get().e()+";"; 
     
    
    }
  public record Sig(Optional<RC> rc, Optional<MName> m, Optional<List<B>> bs, List<Optional<IT>> ts, Optional<IT> ret, Optional<TName> origin, boolean abs, Pos pos){
    public Sig{ assert nonNull(rc,m,bs,ts,ret,origin); assert validOpt(bs,_bs->unmodifiableDistinct(_bs,"bounds")); }
    public Sig(RC rc, MName m, List<B> bs, List<Optional<IT>> ts, IT ret, TName origin, boolean abs, Pos pos){
      this(Optional.of(rc),Optional.of(m),Optional.of(bs),ts,Optional.of(ret),Optional.of(origin),abs,pos);
    }
    public String toString(){
      var bsS= bs.isEmpty() ? "[?]" : bs.get().isEmpty()?"":"["+bs.get().stream().map(Object::toString).collect(Collectors.joining(","))+"]";
      var tsS= ts.isEmpty() ? "" : "("+ts.stream().map(this::t).collect(Collectors.joining(","))+")";
      var rcS= rc.isEmpty()?" ?":rc.get()==RC.imm?"":" "+rc.get().toString();
      var ori= origin.map(o->"@"+o.s()).orElse("@!");
      var mS= m.isPresent()?m.get().toString():"";
      return ""+rcS+" "+mS+bsS+tsS+":"+t(ret)+ori+";";
    }    
    private String t(Optional<IT> ot){ return ot.map(Object::toString).orElse("?"); }
    public Sig withTsT(List<Optional<IT>> ts, IT ret){
      if (ts.equals(this.ts) && this.ret.isPresent() && this.ret.get().equals(ret)){ return this; }
      return new Sig(rc,m,bs,ts,Optional.of(ret),origin,abs,pos);
    }
    public Sig withBsTsT(List<B> bs, List<Optional<IT>> ts, IT ret){
      if (this.bs.isPresent() && bs.equals(this.bs.get()) && ts.equals(this.ts) && this.ret.isPresent() && this.ret.get().equals(ret)){ return this; } 
      return new Sig(rc,m,Optional.of(bs),ts,Optional.of(ret),origin,abs,pos); 
    }
    public boolean isFull(){ return rc.isPresent() && m.isPresent() && bs.isPresent() && ts.stream().allMatch(Optional::isPresent) && ret.isPresent(); }
  }
  public record Impl(Optional<MName> m, List<String> xs, E e){
    public String toString(){
      var xsC= xs.stream().collect(Collectors.joining(", "));
      return " "+m.map(n->n.s()).orElse("")+"("+xsC+")->"+e+";";
    }
    public Impl withE(E e){
      if (e == this.e){ return this; }
      return new Impl(m,xs,e);
    }
  }
}