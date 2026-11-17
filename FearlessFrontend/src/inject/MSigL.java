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

  IT inst(IT t, List<IT> targs){//Note: a wrong number of targs is an error at type system time.
    assert targs.size() == bsArity();
    var ts= Push.of(clsArgs, targs);//performance? we could cache this result since targs is fixed and used over and over
    return TypeRename.of(t, xs, ts);
  }
  static List<IT> toXs(TSpan span, List<String> targetBs){ return targetBs.stream().<IT>map(n -> new IT.X(n, span)).toList(); }
}