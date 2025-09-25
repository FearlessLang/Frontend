package message;

import java.util.function.Supplier;

import fearlessParser.Parser;
import fearlessParser.Token;
import fearlessParser.TokenKind;
import metaParser.MetaParser.Rule;

public record Frame(String name, Supplier<Span> s){
  static private <R> R name(String name, Supplier<Span> s, Supplier<R> r){
    try { return r.get(); }
    catch(RuntimeException|Error t){ 
      if (t instanceof HasFrames f){ f.addFrame(new Frame(name,s)); }
      throw t;
    }
  }
  /*static public <R> R methodCall(Supplier<Span> s, Supplier<R> r){ return name("method call",s,r); }
  static public <R> R roundExp(Supplier<Span> s, Supplier<R> r){ return name("expression in round parenthesis",s,r); }
  static public <R> R literal(Supplier<Span> s, Supplier<R> r){ return name("object literal",s,r); }
  static public <R> R typedLiteral(Supplier<Span> s, Supplier<R> r){ return name("typed object literal",s,r); }
  static public <R> R genericTypes(Supplier<Span> s, Supplier<R> r){ return name("generic types",s,r); }
  static public <R> R methodCallGenericParameters(Supplier<Span> s, Supplier<R> r){ return name("method call generic parameters",s,r); }
  static public <R> R argumentsList(Supplier<Span> s, Supplier<R> r){ return name("arguments list",s,r); }
  static public <R> R nominalPattern(Supplier<Span> s, Supplier<R> r){ return name("nominal pattern",s,r); }
  static public <R> R genericTypesDeclaration(Supplier<Span> s, Supplier<R> r){ return name("generic types declaration",s,r); }
  static public <R> R methodParametersDeclaration(Supplier<Span> s, Supplier<R> r){ return name("method parameters declaration",s,r); }
  static public <R> R genericBoundsDeclaration(Supplier<Span> s, Supplier<R> r){ return name("generic bounds declaration",s,r); }
  static public <R> R typeDeclaration(Supplier<Span> s, Supplier<R> r){ return name("type declaration",s,r); }
  static public <R> R methodDeclaration(Supplier<Span> s, Supplier<R> r){ return name("method declaration",s,r); }
  static public <R> R supertypesDeclaration(Supplier<Span> s, Supplier<R> r){ return name("supertypes declaration",s,r); }*/
  static public <R> Rule<Parser,Token,TokenKind,R> frame(String name,Rule<Parser,Token,TokenKind,R> r){ return p->name(name,p.span(),()->r.parse(p)); }
  
 
}