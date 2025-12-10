package message;

import message.CompactPrinter.*;

final class BestPicker{
  Score best= Score.NONE;
  Compactable pick(PE root){ visit(root,0); return best.k(); }
  void visit(PN n,int depth){
    consider(n,depth+bonus(n));
    switch(n){
      case PX _ -> {}
      case PTX _ -> {}
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
    if (CompactPrinter.showTargs(x.rc(),x.targs().size())){ for (var t: x.targs()){ visit(t,depth); } }
    if (!x.k().isCompactable()){ return; }
    visit(x.recv(),depth);
    for (var a: x.args()){ visit(a,depth); }
  }
  void visitPLit(PLit x,int depth){
    boolean cVisible= x.k().isCompactable() || x.priv();
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
    static final Score NONE= new Score(-1, Compactable.NO);
    Score best(Score o){ return o.score > score ? o : this; } // stable on ties
  }
  static int bonus(PN n){
    if (n instanceof PM){ return 10; }
    if (n instanceof PCall){ return 1; }
    if (n instanceof PC){ return 1; }
    if (n instanceof PLit){ return 1; }
    return 1;
  }
}