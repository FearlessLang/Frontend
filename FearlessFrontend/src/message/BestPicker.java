package message;

import message.CompactPrinter.*;

final class BestPicker{
  Score best= Score.none;
  Compactable pick(PE root){ visit(root,0); return best.k(); }
  void visit(PN n,int depth){
    consider(n,depth+bonus(n));
    switch (n){
      case PX _, PTX _ -> {}
      case PTypeE x -> visit(x.t(), depth + 1);
      case PTRCC x -> visit(x.c(), depth + 1);
      case PC x -> visitPC(x, depth + 1);
      case PCall x -> visitPCall(x, depth + 1);
      case PLit x -> visitPLit(x, depth + 1);
      case PM x -> visitPM(x, depth + 1);
    }
  }
  void visitPC(PC x,int depth){
    if (!x.k().isCompactable()){ return; }
    for (var t: x.ts()){ visit(t,depth); }
  }
  void visitPCall(PCall x,int depth){
    var targsVisible= CompactPrinter.showTargs(x.rc(),x.targs().size());
    if (targsVisible){ for (var t: x.targs()){ visit(t,depth); } }
    if (!x.k().isCompactable()){ return; }
    visit(x.recv(),depth);
    for (var a: x.args()){ visit(a,depth); }
  }
  void visitPLit(PLit x,int depth){
    var cVisible= x.k().isCompactable() || x.priv();
    if (cVisible){ for (var a: x.cs()){ visit(a,depth); } }
    if (!x.k().isCompactable()){ return; }
    for (var m: x.ms()){ visit(m,depth); }
  }
  void visitPM(PM x,int depth){
    if (x.k().isCompactable()){
      for (var t: x.ts()){ visit(t,depth); }
      visit(x.ret(),depth);
    }
    x.body().ifPresent(b->visit(b,depth));
  }
  void consider(PN n, int score){
    if (!n.k().isCompactable()){ return; }
    if (score > best.score){ best= new Score(score,n.k()); }
  }
  record Score(int score, Compactable k){
    static final Score none= new Score(-1, Compactable.no);
  }
  static int bonus(PN n){ return n instanceof PM ? 10 : 1; }
}