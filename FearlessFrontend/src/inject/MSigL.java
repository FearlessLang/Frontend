package inject;

import java.util.List;

import core.B;
import core.RC;
import core.TSpan;
import inference.IT;
import utils.Push;

record MSigL(RC rc, List<String> xs, List<B> clsBs, List<IT> clsArgs, List<B> methBs, List<IT> ps0, IT ret0){
  int nCls(){ return clsArgs.size(); }
  int bsArity(){ return methBs.size(); }

  IT ret(List<IT> targs){ return inst(ret0, targs); }

  MSigL withClsArgs(List<IT> clsArgs){
    assert clsArgs.size() == this.clsArgs.size();
    return new MSigL(rc, xs, clsBs, clsArgs, methBs, ps0, ret0);
  }

  IT inst(IT t, List<IT> targs){//Note: this will eventually become an error at type system time.
    targs= fixTargs(targs, bsArity());
    var ts= Push.of(clsArgs,targs);//performance? we could cache this result since targs is fixed and used over and over
    return TypeRename.of(t, xs, ts);
  }
  static List<IT> fixTargs(List<IT> targs, int n){
    var k= targs.size();
    if (k > n){ return targs.subList(0, n); }
    return Push.of(targs, InjectionSteps.qMarks(n-k));
  }
  static List<IT> toXs(TSpan span,List<String> targetBs){ return targetBs.stream().<IT>map(n->new IT.X(n,span)).toList(); }
}