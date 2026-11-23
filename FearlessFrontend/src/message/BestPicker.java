package message;

import message.CompactPrinter.*;

final class BestPicker{
  int bestScore= -1;
  Compactable best= Compactable.no;
  Compactable pick(PE root){ visit(root, 0); return best; }
  void visit(PN n, int depth){
    consider(n, depth+(n instanceof PM ? 10 : 1));
    switch (n){
      case PText _ -> {}
      case PTypeE(var t) -> visit(t, depth + 1);
      case PTRCC(_, var c) -> visit(c, depth + 1);
      case PC x -> visitPC(x, depth + 1);
      case PCall x -> visitPCall(x, depth + 1);
      case PLit x -> visitPLit(x, depth + 1);
      case PM x -> visitPM(x, depth + 1);
    }
  }
  void visitPC(PC x, int depth){
    if (x.k().compacted){ return; }
    for (var t : x.ts()){ visit(t, depth); }
  }
  void visitPCall(PCall x, int depth){
    if (!x.k().pinned){ for (var t : x.targs()){ visit(t, depth); } }
    if (x.k().compacted){ return; }
    visit(x.recv(), depth);
    for (var a : x.args()){ visit(a, depth); }
  }
  void visitPLit(PLit x, int depth){
    if (x.csShown() && !x.k().pinned){ for (var a : x.cs()){ visit(a, depth); } }
    if (x.k().compacted){ return; }
    for (var m : x.ms()){ visit(m, depth); }
  }
  void visitPM(PM x, int depth){
    if (!x.k().pinned){
      for (var t : x.ts()){ visit(t, depth); }
      visit(x.ret(), depth);
    }
    if (!x.k().compacted){ x.body().ifPresent(b -> visit(b, depth)); }
  }
  void consider(PN n, int score){
    if (n.k().compacted || n.k().pinned){ return; }
    if (score > bestScore){ bestScore = score; best = n.k(); }
  }
}
