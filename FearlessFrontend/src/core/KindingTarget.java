package core;

import fearlessFullGrammar.TSpan;

public sealed interface KindingTarget permits KindingTarget.CallKinding,T.RCC, T.C{
  TSpan span();
  record CallKinding(T.C t,E.Call c) implements KindingTarget{
    public TSpan span(){ return c.span(); }
    }
}
