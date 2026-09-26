package fearlessParser;

import fearlessFullGrammar.E;

public final class HasImplicitVisitor{
  private HasImplicitVisitor(){}
  public static boolean of(E e){
    return switch (e){
      case E.X _ -> false;
      case E.Round(var inner) -> of(inner);
      case E.Implicit _ -> true;
      //correctly not entering in literals. The :: is literal scoped, so a :: in the literal would be in the inner scope
      case E.TypedLiteral _, E.DeclarationLiteral _, E.Literal _ -> false;
      case E.Call c -> of(c.e()) || c.es().stream().anyMatch(HasImplicitVisitor::of);
    };
  }
}
