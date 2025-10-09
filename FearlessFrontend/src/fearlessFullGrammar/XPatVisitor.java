package fearlessFullGrammar;

public interface XPatVisitor<R>{
  R visitXPatName(XPat.Name n);
  R visitXPatDestruct(XPat.Destruct d);
}