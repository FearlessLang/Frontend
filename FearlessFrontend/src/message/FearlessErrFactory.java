package message;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import fearlessFullGrammar.M;
import fearlessFullGrammar.Sig;
import fearlessFullGrammar.T;
import fearlessFullGrammar.ToString;
import fearlessParser.Parser;
import fearlessParser.RC;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import static fearlessParser.TokenKind.*;
import fearlessParser.Tokenizer;
import metaParser.ErrFactory;
import metaParser.Frame;
import metaParser.Message;
import metaParser.NameSuggester;
import metaParser.Span;
import utils.Bug;

import static offensiveUtils.Require.*;

public class FearlessErrFactory implements ErrFactory<Token,TokenKind,FearlessException,Tokenizer,Parser,FearlessErrFactory>{

  @Override public FearlessException illegalCharAt(Span at, int cp, Tokenizer tokenizer){
    String head= "Illegal character "+Message.displayChar(cp);
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  @Override public FearlessException missing(Span at, String what, List<TokenKind> expectedLabels, Parser parser){
    assert nonNull(at,what,expectedLabels);
    String label= what.isBlank() ? "element" : what;
    String msg = "Missing " + label + ".\n"+expected(expectedLabels);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }

  @Override public FearlessException extraContent(Span from, String what, Collection<TokenKind> expectedTerminatorTokens, Parser parser){
    assert nonNull(from,parser,expectedTerminatorTokens);
    String msg= "Extra content in the current group.\n";
    if (!expectedTerminatorTokens.isEmpty()){
      var instead= "Instead, expected "+what;
      msg += expected("",instead+": ",instead+" one of: ",expectedTerminatorTokens,tk->tk.human);
    }
    var here= parser.peek().get().span(from.fileName());
    return Code.ExtraTokenInGroup.of(msg).addSpan(here).addSpan(from);
  }
  @Override public FearlessException probeStalledIn(String groupLabel, Span at, int startIdx, int endIdx, Parser parser){
    String head= "Probe stalled while scanning " + groupLabel;
    return Code.ProbeError.of(head).addSpan(at);
  }
  @Override public FearlessException badProbeDropIn(String groupLabel, Span at, int startIdx, int endIdx, int drop, Parser parser){
    String msg= "Probe returned invalid drop=" + drop
      + " in " + groupLabel + " at [" + startIdx + ".." + endIdx + "]";
    return Code.ProbeError.of(msg).addSpan(at);
  }
  public FearlessException noClose(Span at){
    return Code.InterpolationNoClose.of(
      "Unclosed string interpolation placeholder").addSpan(at);
  }
  public FearlessException noOpen(Span at){
    return Code.InterpolationNoOpen.of(
      "Unopened string interpolation placeholder").addSpan(at);
  }
  public FearlessException moreOpen(Span at){
    return Code.InterpolationNoClose.of(
      "String interpolation placeholder opened inside interpolation expression.\n"
      +"Note: \"{\" can not be used in single \"#\" interpolation expressions. Use at least \"##\".").addSpan(at);
  }
  public FearlessException disallowedReadHMutH(Span at, RC rc){
    return Code.UnexpectedToken.of(
      "Capability "+rc+"""
       used.
      Capabilities readH and mutH are not allowed on closures
      Use one of read, mut, imm, iso.      
      """).addSpan(at);
  }
  public FearlessException disallowedSigRC(Span at, RC rc){
    return Code.UnexpectedToken.of(
      "Capability "+rc+"""
       used.
      Capabilities iso, readH and mutH are not allowed on method declarations.
      Use one of read, mut, imm.      
      """).addSpan(at);
  }
  public FearlessException disallowedSig(Span at, Sig sig){
    return Code.WellFormedness.of(
      "A literal signature can only be either fully typed or fully untyped.\n"
    + "Signature "+Message.displayString(ToString.sig(sig))+" has some, but not all, type informations.\n"
      ).addSpan(at);
  }
  public FearlessException disallowedPackageNotEmpty(Span at){
    return Code.UnexpectedToken.of(
      "The package declaration must be at the very beginning of the file.\n"
    ).addSpan(at);
  }
  public FearlessException disallowedRoleNotEmpty(Span at){
    return Code.UnexpectedToken.of(
      "There can be a single role declaration in the file header.\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedMap(Span at, String what){
    return Code.UnexpectedToken.of(
      "There is already an entry in the mapping for "+what+".\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedUseSource(Span at, String what){
    return Code.UnexpectedToken.of(
        "There is already an entry in the using with source "+Message.displayString(what)+".\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedUseDest(Span at, String what){
    return Code.UnexpectedToken.of(
        "There is already an entry in the using with destination "+Message.displayString(what)+".\n"
    ).addSpan(at);
  }
  public FearlessException duplicatedImpl(List<T.C> cs, Span at){
    T.C c= redeclaredElement(cs);
    return Code.WellFormedness.of(
      "Duplicated supertype in type declaration: "+Message.displayString(ToString.c(c))+".\n"
    ).addSpan(at);
  }

  public FearlessException nameNotInScope(Token name, Span at, List<String> inScope){
    return Code.UnexpectedToken.of(() -> {
      var scope= inScope.isEmpty()
        ? "No names are in scope here.\n"
        : NameSuggester.suggest(name.content(), inScope);
      return "Name "+Message.displayString(name.content())+" is not in scope\n" + scope;
    }).addSpan(at);
  }
  public FearlessException nameRedeclared(Token c, Span at){
    return Code.UnexpectedToken.of("Name "+Message.displayString(c.content())+" already in scope").addSpan(at);
  }
  private <X> X redeclaredElement(List<X> es){
    int i= 0;
    for (var e:es){
      int first= i++;
      int last=  es.lastIndexOf(e);
      if (first != last){ return e; }
    }
    throw Bug.unreachable();
  }
  private Span redeclaredMethSpan(List<M> ms,Predicate<M> p, Span at){
    M m= ms.reversed().stream().filter(p).findFirst().get();
    return new Span(at.fileName(),m.pos().line(),m.pos().column(),m.pos().line(),m.pos().column() + 100);  
  }
  private Span redeclaredMethSpan(List<M> ms,Parser.RCMName n, Span at){
    Predicate<M> p= mi->mi.sig()
      .map(s->s.m().equals(Optional.of(n.name())) && s.rc().equals(n.rc()))
      .orElse(false);
    return redeclaredMethSpan(ms,p,at);
  }
  private Span redeclaredMethSpan(List<M> ms, int count, Span at){
    Predicate<M> p= mi->parCount(mi) == count;
    return redeclaredMethSpan(ms,p,at);
  }
  public FearlessException methNameRedeclared(List<M> ms,List<Parser.RCMName> names, Span at){
    var name= redeclaredElement(names);
    Span s= redeclaredMethSpan(ms,name,at);
    return Code.WellFormedness.of(
      "Method "+Message.displayString(name.name().s())+" redeclared.\n"
    + "A method with the same name, arity and reference capability is already present.\n")
      .addSpan(s).addSpan(at);
  }
  public int parCount(M m){
    if(m.sig().isPresent() && m.sig().get().m().isPresent()){ return -1; }
    return m.sig().map(s->s.parameters().size()).orElse(0) + (m.hasImplicit()?1:0);    
  }
  public FearlessException methNoNameRedeclared(List<M> ms, List<Integer> noNames, Span at){
    var count= redeclaredElement(noNames);
    Span s= redeclaredMethSpan(ms,count,at);
    return Code.WellFormedness.of(
      "Method with inferred name and "+count+" parameter redeclared.\n"
    + "A method with the inferred name and the same parameter count is already present above.\n")
      .addSpan(s).addSpan(at);
  }
  public FearlessException typeNameConflictsGeneric(Token name, Span at){
    return Code.UnexpectedToken.of("Name "+Message.displayString(name.content())+" is used as a type name, but  "+Message.displayString(name.content())+" is already a generic type parameter in scope").addSpan(at);
  }
  public FearlessException privateTypeName(Token name, Span at){
    var sep= name.content().indexOf("._");
    String sName= name.content().substring(sep+1);
    String pName= name.content().substring(0,sep);
    return Code.UnexpectedToken.of(
      "Code is attempting to use private name "+Message.displayString(sName)
      +" from package "+Message.displayString(pName)
      +".\nType names starting with \"_\" can only be used in their own package, and only by their simple name.\n").addSpan(at);
  }
  public FearlessException missingExprAfterEq(Span at){
    return Code.UnexpectedToken.of("""
      Missing expression after "=" in the equals sugar.
      Use: ".m x = expression" or ".m {a,b} = expression".
      """).addSpan(at);
  }
  public FearlessException parameterNameExpected(Span at){
    return Code.UnexpectedToken.of("Parameter name expected").addSpan(at);
  }
  public FearlessException spaceBeforeId(Span at, String id){
    return Code.UnexpectedToken.of(
      "Found spacing between closed curly and destruct id \""+ id+"\"."
      +"\nThere need to be no space between the closed curly and the destruct id.")
      .addSpan(at);
  }
  public FearlessException badBound(String name, Span at){
    return Code.UnexpectedToken.of("Invalid bound for generic "+name+"""
      
      Only '*' or '**' are allowed here
      Write: X:*   meaning mut,read,imm
         or: X:**  meaning everything
      """).addSpan(at);
  }
  public FearlessException genericNotInScope(Token X, Span at, Collection<String> Xs){
    return Code.UnexpectedToken.of(() ->
      "Generic type "+Message.displayString(X.content())+" is not in scope.\n" +
      expected(
        "No generic parameters are declared here",
        "Declared generics: ","Declared generics: ",
        Xs,s->s)).addSpan(at);
  }
  public FearlessException duplicateParamInMethodSignature(Span at, String name){
    return Code.UnexpectedToken.of(
      "A method signature cannot declare multiple parameters with the same name\n"
      +"Parameter "+Message.displayString(name)+" is repeated").addSpan(at);
  }
  public FearlessException duplicateGenericInMethodSignature(Span at, String name){
    return Code.UnexpectedToken.of(
      "A method signature cannot declare multiple generic type parameters with the same name\n"
      +"Generic type parameter "+Message.displayString(name)+" is repeated").addSpan(at);
  }
  public String context(){return "File ended while parsing a "; }
  private static String expected(Collection<TokenKind> items){ return expected("","Expected: ","Expected one of: ",items,tk->tk.human); }
  private static <EE> String expected(String pre0, String pre1, String preMany, Collection<EE> items, Function<EE,String> f){
    if (items.isEmpty()){ return pre0.isEmpty()? "" : pre0+".\n"; }
    String res= items.stream()
        .map(e->Message.displayString(f.apply(e)))
        .collect(Collectors.joining(", "));
    if (items.size() == 1){ return pre1 + res + ".\n"; }
    return preMany + res + ".\n";
  }
  @Override public FearlessException unrecognizedTextAt(Span at, String what, Tokenizer tokenizer){
    String head= what.isBlank()
      ? "Unrecognized text."
      : "Unrecognized text " + Message.displayString(what)+".";
    return Code.UnexpectedToken.of(head).addFrame(new Frame("", at));
  }
  public FearlessException missingSemicolonOrOperator(Span at){
    return Code.MissingSeparator.of(
      "There is a missing \";\", operator or method name here or before.\n").addSpan(at);
  }
  public FearlessException signedLiteral(Span at,Token t){
    return Code.UnexpectedToken.of(
      "Here "+Message.displayString(t.content())
      +" is seen as a single signed literal, not as a +/- operator followed by a literal.\n"
      +"Write \"1 + 2\" not \"1+2\".\n"
      +"Write \"+1 + +2\" not \"+1+2\".\n"
      +"Write \"+0.53 + +2.32\" not \"0.53+2.32\".\n"
      +"Write \"+3/2 + +4/5\" not \"3/2+4/5\"."
      ).addSpan(at);
  }
  @Override public FearlessException groupHalt(
      Token open, Token stop, Collection<TokenKind> expectedClosers, LikelyCause likely,
      Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, tokenizer, likely);

    var file= tokenizer.fileName();
    boolean sof= open.is(_SOF);
    boolean eof= stop.is(_EOF);
    boolean isCloser= stop.is(CRound, CSquare, CCurly, CCurlyId);
    boolean isBarrier= !eof && !isCloser;

    String openLabel= Message.displayString(open.kind().human);
    String stopLabel= eof ? "end of group" : Message.displayString(stop.kind().human);
    String base=
      sof
        ?"Unopened " + stopLabel + ".\n"
      :eof
        ? context() + openLabel + " group.\n"
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
    var span = eof ? open.span(file) : metaParser.Token.makeSpan(file, open, stop);
    var code= sof ? Code.Unopened : (eof || isBarrier) ? Code.Unclosed : Code.UnexpectedToken;
    return code.of(base + hint+ expected).addFrame("groups of parenthesis",span);
  }
  @Override public FearlessException eatenCloserBetween(
      Token open, Token stop, Collection<TokenKind> expectedClosers,
      Token hiddenFragment, Token hiddenContainer, Tokenizer tokenizer){
    assert nonNull(open, stop, expectedClosers, hiddenFragment, hiddenContainer, tokenizer);

    var file= tokenizer.fileName();
    String where= BadTokens.describeFree(hiddenContainer);
    var other= "Otherwise expected";
    String msg=
      "Unclosed " + Message.displayString(open.kind().human) + " group.\n"
    + "Found a matching closer inside a" + where + " between here and the stopping point.\n"
    + "Did you mean to place the closer outside the" + where + "?\n"
    + expected("",other+": ", other+" one of: ",expectedClosers,tk->tk.human);

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
      "Unopened " + Message.displayString(stop.kind().human) + ".\n"
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
    + "Found instead: " + Message.displayString(found.content()) + ".\n"
    + expected(expectedTokens);
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
  public FearlessException badTopSelfName(Span at, String name){
    String msg= "Self name "+name+" invalid in a top level type.\n"
      + "Top level types self names can only be \" 'this \".\n";
    return Code.WellFormedness.of(msg).addSpan(at);
  }
  public FearlessException noAbstractMethod(Sig sig, Span at){
    String msg= "Abstract method declaration for "+Message.displayString(ToString.sig(sig))
      +".\nOnly top level methods can be abstract.\n";
    return Code.WellFormedness.of(msg).addSpan(at);
  }
  public FearlessException inconsistentStrInter(Span at,boolean simpleToU){
    String base= simpleToU ? "Simple" : "Unicode";
    String alt= simpleToU ? "Unicode" : "Simple";
    String msg= "String interpolation changes midway from "+base+" to "+alt+".\n";
    return Code.UnexpectedToken.of(msg).addSpan(at);
  }
}