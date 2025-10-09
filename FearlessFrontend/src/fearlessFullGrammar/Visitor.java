package fearlessFullGrammar;

public interface Visitor<RE,RT,RXPat> extends EVisitor<RE>,TVisitor<RT>,XPatVisitor<RXPat>{}