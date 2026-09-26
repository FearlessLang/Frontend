package message;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import core.FearlessException;
import core.MName;
import core.RC;
import core.TName;
import fearlessFullGrammar.M;
import fearlessFullGrammar.Sig;
import fearlessFullGrammar.T;
import fearlessFullGrammar.XPat;
import fearlessParser.Parser;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import static fearlessParser.TokenKind.*;
import fearlessParser.Tokenizer;
import metaParser.ErrFactory;
import metaParser.Frame;
import metaParser.Message;
import metaParser.NameSuggester;
import metaParser.Span;
import utils.Join;
import utils.Push;

import static message.Err.*;
import static offensiveUtils.Require.*;

public class FearlessErrFactory implements ErrFactory<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>{
  Optional<TName> lastTop= Optional.empty();
  public void noteTop(TName t){ lastTop= Optional.of(t); }
  @Override public FearlessException illegalCharAt(Span at, int cp, Tokenizer tokenizer){
    return Code.UnexpectedToken.of("Illegal character "+Message.displayChar(cp)).addFrame(new Frame("", at));
  }
  @Override public FearlessException missing(Span at, String what, List<TokenKind> expectedLabels, Parser parser){
    assert nonNull(at,what,expectedLabels);
    String label= what.isBlank() ? "element" : what;
    String msg = "Missing " + label + ".\n"+expected(expectedLabels);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  public FearlessException topLevelSemicolon(Span at){ return Code.UnexpectedToken.of(this::topLevelSemicolonMsg).addSpan(at); }
  private String topLevelSemicolonMsg(){
    if (lastTop.isEmpty()){
      return "Extra semicolon before the first top level type declarations.\n"
           + "Remove this semicolon.\n";
    }
    var n= staticTypeDecName(lastTop.get());
    String hint= lastTop.get().s()+(lastTop.get().arity() == 0 ? ":..{...}" : "[..]:..{...}");
    return "Top level type declarations do not end with \";\".\n"
         + "The defintion of " + n + " ends with a semicolon. Remove it.\n"
         + "Write: "+disp(hint)+"\n"
         + "Not:   "+disp(hint+";")+"\n";
  }
  public FearlessException topLevelNotATypeDeclaration(Span at, String found){
    return Code.UnexpectedToken.of(()->
      lastTop.map(t->"This should probably be inside the declaration of "+staticTypeDecName(t)+".\n")
        .orElse("This is not a top level type declaration.\n")
      + "Top level code can only contain type declarations.\n"
      + "A type declaration starts with a type name, like \"Point:{..}\".\n"
      + "Found instead: " + disp(found) + ".\n"
      + "Likely cause: an extra \"}\" closed a type declaration unintentionally.\n"
      ).addSpan(at);
  }
  @Override public FearlessException extraContent(Span from, String what, Collection<TokenKind> expectedTerminatorTokens, Parser parser){
    assert nonNull(from,parser,expectedTerminatorTokens);
    var instead= "Expected "+what;
    String msg= expected("Extra content in the current group",instead+": ",instead+".\nExpected one of: ",expectedTerminatorTokens,tk->tk.human);
    var here= parser.peek().get().span(from.fileName());
    return Code.ExtraTokenInGroup.of(msg).addSpan(here).addSpan(from);
  }
  @Override public FearlessException probeStalledIn(String groupLabel, Span at, int startIdx, int endIdx, Parser parser){
    return Code.ProbeError.of("Probe stalled while scanning " + groupLabel).addSpan(at);
  }
  @Override public FearlessException badProbeDropIn(String groupLabel, Span at, int startIdx, int endIdx, int drop, Parser parser){
    String msg= "Probe returned invalid drop=" + drop
      + " in " + groupLabel + " at [" + startIdx + ".." + endIdx + "]";
    return Code.ProbeError.of(msg).addSpan(at);
  }
  public FearlessException disallowedReadHMutH(Span at, RC rc){
    return disallowedRc(at,rc,"readH and mutH","object literals","read, mut, imm, iso");
  }
  public FearlessException disallowedSigRC(Span at, RC rc){
    return disallowedRc(at,rc,"iso, readH and mutH","method declarations","read, mut, imm");
  }
  private FearlessException disallowedRc(Span at, RC rc, String disallowed, String where, String allowed){
    return Code.UnexpectedToken.of(
      "Capability "+rc+" used.\n"
    + "Capabilities "+disallowed+" are not allowed on "+where+".\n"
    + "Use one of "+allowed+".\n").addSpan(at);
  }
  public FearlessException forgotSpace(Span at,String name){
    return Code.UnexpectedToken.of(
      "Did you forget a space in "+disp(name)+"?\n"
      +"Did you mean "+disp(name.substring(0,name.length()-2)+" ->")+"?\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedMap(Span at, String what, String in){
    return Code.UnexpectedToken.of(
      "There is already an entry in the mapping for "+disp(what)+" in "+disp(in)+".\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedUse(Span at, String what, String kind){
    return Code.UnexpectedToken.of(
        "There is already an entry in the using with "+kind+" "+disp(what)+".\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedImpl(List<T.C> cs, Span at){
    T.C c= redeclaredElement(cs);
    return Code.WellFormedness.of(
      "Duplicated supertype in type declaration: "+staticTypeDecName(c.name())+".\n"
    ).addSpan(at);
  }

  public FearlessException nameNotInScope(Token name, Span at, List<String> inScope){
    return Code.UnexpectedToken.of(()->nameNotInScopeMsg(name,inScope)).addSpan(at);
  }
  private static String nameNotInScopeMsg(Token name, List<String> inScope){
    var scope= inScope.isEmpty()
      ? "No names are in scope here.\n"
      : NameSuggester.suggest(name.content(), inScope.stream().sorted().toList());
    return "Name "+disp(name.content())+" is not in scope.\n" + scope;
  }
  public FearlessException nameRedeclared(Token c, Span at){
    return Code.UnexpectedToken.of("Name "+disp(c.content())+" already in scope.").addSpan(at);
  }
  private <X> X redeclaredElement(List<X> es){
    return IntStream.range(0, es.size())
      .filter(i->i != es.lastIndexOf(es.get(i)))
      .mapToObj(es::get)
      .findFirst().get();
  }
  private Span redeclaredMethSpan(List<M> ms,Predicate<M> p){ return ms.reversed().stream().filter(p).findFirst().get().span().inner; }
  public FearlessException methNameRedeclared(List<M> ms,List<Parser.RCMName> names, Span at){
    var name= redeclaredElement(names);
    Predicate<M> p= mi->mi.sig().stream().anyMatch(sig->sig.m().equals(Optional.of(name.name())) && sig.rc().equals(name.rc()));
    Span s= redeclaredMethSpan(ms,p);
    return Code.WellFormedness.of(
      "Method "+disp(name.name().s())+" redeclared.\n"
    + "A method with the same name, arity and reference capability is already present.\n")
      .addSpan(s).addSpan(at);
  }
  public FearlessException methMixedExplicitRC(List<M> ms, MName name, Span at){
    Predicate<M> p= mi->mi.sig().stream().anyMatch(s->s.m().equals(Optional.of(name)) && s.rc().isEmpty());
    Span s= redeclaredMethSpan(ms,p);
    return Code.WellFormedness.of(
      "Method "+disp(name.s())+" mixes an explicit and an inferred reference capability.\n"
    + "Once one overload of "+disp(name.s())+" declares a reference capability, every overload of that method must.\n"
    ).addSpan(s).addSpan(at);
  }
  public int parCount(M m){//-1 == explicitly named method
    if (m.sig().flatMap(Sig::m).isPresent()){ return -1; }
    return m.sig().map(s->s.parameters().size()).orElse(0) + (m.hasImplicit()?1:0);
  }
  public FearlessException missingDotBeforeMethodName(Span at, String name){
    return Code.WellFormedness.of(
      "Method declaration missing \".\" before the name.\n"
    + "To declare a method named "+disp(name)+", write \"."+name+"\" (dot "+name+").\n"
    ).addSpan(at);
  }
  private Stream<String> potentialMethodNames(M m){
    return m.sig().stream()
      .flatMap(s->s.parameters().stream().limit(1))
      .flatMap(p->p.xp().stream())
      .flatMap(xp->xp instanceof XPat.Name n ? Stream.of(n.x().name()) : Stream.empty());
  }
  public FearlessException methNoNameRedeclared(List<M> ms, List<Integer> noNames, Span at){
    var count= redeclaredElement(noNames);
    Span s= redeclaredMethSpan(ms,mi->parCount(mi) == count);
    List<String> hints= ms.stream()
      .filter(m->parCount(m) == count)
      .flatMap(this::potentialMethodNames)
      .distinct().toList();
    String base= "Method with inferred name and "+count+" parameter redeclared.\n"
    + "A method with the inferred name and the same parameter count is already present above.\n";
    if (hints.isEmpty()){ return Code.WellFormedness.of(base).addSpan(s).addSpan(at); }
    var ex= hints.getFirst();
    return Code.WellFormedness.of(
      base
    + "Likely cause: method declaration missing \".\" before the name.\n"
    + Join.of(hints.stream().map(Err::disp),
      "Found unnamed methods with parameters: ",", ",".\n")
    + "To declare a method named "+disp(ex)+", write \"."+ex+"\" (dot "+ex+").\n"
    + "Without the dot, "+disp(ex)+" is interpreted as a parameter name for an anonymous method.\n"
    ).addSpan(s).addSpan(at);
  }
  public FearlessException typeNameConflictsGeneric(Token name, Span at){
    return Code.UnexpectedToken.of("Name "+disp(name.content())+" is used as a type name, but "+disp(name.content())+" is already a generic type parameter in scope.").addSpan(at);
  }
  public FearlessException privateTypeName(Token name, Span at){
    var sep= name.content().indexOf("._");
    String sName= name.content().substring(sep+1);
    String pName= name.content().substring(0,sep);
    return Code.UnexpectedToken.of(
      "Code is attempting to use private name "+disp(sName)
      +" from package "+disp(pName)
      +".\nType names starting with \"_\" can only be used in their own package, and only by their simple name.\n").addSpan(at);
  }
  public FearlessException missingExprAfterEq(Span at){
    return Code.UnexpectedToken.of("""
      Missing expression after "=" in the equals sugar.
      Use: ".m x = expression" or ".m {a,b} = expression".
      """).addSpan(at);
  }
  public FearlessException parameterNameExpected(Span at){
    return Code.UnexpectedToken.of("Parameter name expected.").addSpan(at);
  }
  public FearlessException spaceBeforeId(Span at, String id){
    return Code.UnexpectedToken.of(
      "Found spacing between closed curly and destruct id "+disp(id)+"."
      +"\nThere must be no space between the closed curly and the destruct id.")
      .addSpan(at);
  }
  public FearlessException emptyDestructPattern(Span at){
    return Code.UnexpectedToken.of(
      "This destructuring pattern extracts nothing.\n"
      +"Write at least one chain, for example {.a}, instead of an empty {}.")
      .addSpan(at);
  }
  public FearlessException emptyDestructChain(Span at){
    return Code.UnexpectedToken.of(
      "This destructuring pattern has an empty chain between commas.\n"
      +"Each comma must separate two non-empty chains; remove the stray comma, for example write {.a,.b} instead of {.a,,.b} or {,.a}.")
      .addSpan(at);
  }
  public FearlessException badBound(T.X name, Span at){
    return Code.UnexpectedToken.of("Invalid bound for generic "+disp(name.name())+"""

      Only "*" or "**" are allowed here
      Write: X:*   meaning mut,read,imm
         or: X:**  meaning everything.
      """).addSpan(at);
  }
  public FearlessException genericNotInScope(Token X, Span at, Collection<String> Xs){
    return Code.UnexpectedToken.of(()->
      "Generic type "+disp(X.content())+" is not in scope.\n" +
      expected(
        "No generic parameters are declared here",
        "Declared generics: ","Declared generics: ",
        Xs,s->s)).addSpan(at);
  }
  public FearlessException genericNotFunnelled(Token X, Span at, String owner, List<String> Xs){
    String x= disp(X.content());
    String dec= disp(owner);
    String funnelled= disp(Join.of(Push.of(Xs,X.content()).stream().map(s->s+":.."),owner+"[",",","]",""));
    return Code.UnexpectedToken.of(
      "Generic type "+x+" is not in scope inside the type declaration "+dec+".\n"
      +"A type declaration only sees the generic types it declares itself; "
      +expected("here "+dec+" declares none","here "+dec+" declares ","here "+dec+" declares ",Xs,s->s)
      +"Hint: funnel "+x+" into "+dec+" by writing "+funnelled+", restating the bounds of "+x+".").addSpan(at);
  }
  public FearlessException patternNameRedeclared(Span at, String name){
    return Code.UnexpectedToken.of("Name "+disp(name)+" already in scope.\n"
      +"It is declared by a nominal pattern: a pattern like \"{.a.b, .c}id\" declares the names \"bid\" and \"cid\".\n").addSpan(at);
  }
  public FearlessException duplicateParamInMethodSignature(Span at, String name){
    return Code.UnexpectedToken.of(
      "A method signature cannot declare multiple parameters with the same name\n"
      +"Parameter "+disp(name)+" is repeated").addSpan(at);
  }
  public FearlessException duplicateGenericInMethodSignature(Span at, String name){
    return Code.UnexpectedToken.of(
      "A method signature cannot declare multiple generic type parameters with the same name\n"
      +"Generic type parameter "+disp(name)+" is repeated").addSpan(at);
  }
  private static String expected(Collection<TokenKind> items){ return expected("","Expected: ","Expected one of: ",items,tk->tk.human); }
  private static <EE> String expected(String pre0, String pre1, String preMany, Collection<EE> items, Function<EE,String> f){
    return Join.of(items.stream().map(e->disp(f.apply(e))),
      items.size() == 1 ? pre1 : preMany,", ",".\n",pre0.isEmpty()? "" : pre0+".\n");
  }
  @Override public FearlessException unrecognizedTextAt(Span at, String what, Tokenizer tokenizer){
    String head= what.isBlank()
      ? "Unrecognized text."
      : "Unrecognized text " + disp(what)+".";
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  public FearlessException missingSemicolonOrOperator(Span at){
    return Code.MissingSeparator.of(
      "There is a missing semicolon \";\", operator, or method name here or earlier.\n"
      ).addSpan(at);
  }
  @Override public FearlessException groupHalt(
      Token open, Token stop, Collection<TokenKind> expectedClosers, LikelyCause likely,
      Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, tokenizer, likely);
    var file= tokenizer.fileName();
    var sof= open.is(_SOF);
    var eof= stop.is(_EOF);
    var isCloser= stop.is(CRound, CSquare, CCurly, CCurlyId);
    var isBarrier= !eof && !isCloser;
    String openLabel= disp(open.kind().human);
    String stopLabel= eof ? "end of group" : disp(stop.kind().human);
    String base=
      sof
        ?"Unopened " + stopLabel + ".\n"
      :eof
        ? "File ended while parsing a " + openLabel + " group.\n"
      : isBarrier
        ? "Unclosed " + openLabel + " group before " + stopLabel + ".\n"
        : ("Wrong closer for " + openLabel + " group.\nFound instead: " + stopLabel + ".\n");
    String hint= switch (likely){
      case MissingCloser -> "Insert the expected closer before " + stopLabel + ".\n";
      case StrayCloser   -> "This "+stopLabel+" may be unintended.\n";
      case StrayOpener   -> "This "+openLabel+" may be unintended.\n";
      case MissingOpener -> "Insert the matching opener before this closer.\n";
      case Unknown       -> "";
    };
    var other= hint.isEmpty()?"Expected":"Otherwise expected";
    var expected= sof?"":expected("",other+": ", other+" one of: ",expectedClosers,tk->tk.human);
    var span= eof ? open.span(file) : metaParser.Token.makeSpan(file, open, stop);
    var code= sof ? Code.Unopened : (eof || isBarrier) ? Code.Unclosed : Code.UnexpectedToken;
    return code.of(base + hint+ expected).addFrame("groups of parenthesis",span);
  }
  @Override public FearlessException eatenCloserBetween(
      Token open, Token stop, Collection<TokenKind> expectedClosers,
      Token hiddenFragment, Token hiddenContainer, Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, hiddenFragment, hiddenContainer, tokenizer);
    var file= tokenizer.fileName();
    String where= BadTokens.describeFree(hiddenContainer);
    String msg=
      "Unclosed " + disp(open.kind().human) + " group.\n"
    + "Found a matching closer inside a" + where + " between here and the stopping point.\n"
    + "Did you mean to place the closer outside the" + where + "?\n"
    + expected("","Otherwise expected: ","Otherwise expected one of: ",expectedClosers,tk->tk.human);
    var primary= metaParser.Token.makeSpan(file, open, hiddenFragment);
    var secondary= metaParser.Token.makeSpan(file, open, hiddenContainer);
    return Code.Unclosed.of(msg).addFrame("groups of parenthesis",primary).addSpan(secondary);
  }
  @Override public FearlessException eatenOpenerBetween(
      Token open, Token stop, Collection<TokenKind> expectedClosers,
      Token hiddenFragment, Token hiddenContainer, Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, hiddenFragment, hiddenContainer, tokenizer);
    var file= tokenizer.fileName();
    String where= BadTokens.describeFree(hiddenContainer);
    String msg=
      "Unopened " + disp(stop.kind().human) + ".\n"
    + "Found a matching opener hidden inside a" + where + " before this point.\n"
    + "Did you mean to place the opener outside the" + where + "?";
    var primary= metaParser.Token.makeSpan(file, hiddenFragment, stop);
    var secondary= metaParser.Token.makeSpan(file, hiddenContainer, stop);
    return Code.Unopened.of(msg).addSpan(primary).addFrame("groups of parenthesis",secondary);
  }

  @Override public FearlessException missingButFound(
      Span at, String what, Token found, Collection<TokenKind> expectedTokens, Parser parser){
    assert nonNull(at, what, found, expectedTokens);
    String msg=
      "Missing " + (what.isBlank() ? "element" : what) + ".\n"
    + "Found instead: " + disp(found.content()) + ".\n"
    + expected(expectedTokens);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  public FearlessException badTopSelfName(Span at, String name){
    String msg= "Self name "+disp(name)+" is invalid in a top level type.\n"
      + "Top level types self names can only be \"this\".\n";
    return Code.WellFormedness.of(msg).addSpan(at);
  }
  public FearlessException noAbstractMethod(Sig sig, Span at){
    String msg= "Abstract method declaration for "+disp(sig.m().get().s())
      +".\nOnly top level methods can be abstract.\n";
    return Code.WellFormedness.of(msg).addSpan(at);
  }
}