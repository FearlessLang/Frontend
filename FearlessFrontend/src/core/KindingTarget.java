package core;

public sealed interface KindingTarget permits KindingTarget.CallKinding, T.C{
  TSpan span();
  record CallKinding(T.C t,E.Call c) implements KindingTarget{
    @Override public TSpan span(){ return c.span(); }
  }
}
