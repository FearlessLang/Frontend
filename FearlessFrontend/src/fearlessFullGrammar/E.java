package fearlessFullGrammar;

import java.util.*;

import fearlessParser.RC;
import files.Pos;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

public sealed interface E {
  Pos pos();
  <R> R accept(EVisitor<R> v);
  record X(String name, Pos pos) implements E{
    public X{ assert validate(name, "parameter name",LowercaseId); }
    public <R> R accept(EVisitor<R> v){ return v.visitX(this); }
    public String toString(){ return name; }
  }
  record Round(E e) implements E{
    public Round{ assert nonNull(e); }
    public Pos pos(){ return e.pos(); }
    public <R> R accept(EVisitor<R> v){ return v.visitRound(this); }
    public String toString(){ return "("+e+")"; }
  }
  record Literal(Optional<E.X> thisName, List<M> methods,Pos pos) implements E{
    public Literal{
      assert unmodifiable(methods, "L.Full.methods");
      assert nonNull(thisName);
    }
    public <R> R accept(EVisitor<R> v){ return v.visitLiteral(this); }
    public String toString(){ return "Literal"+thisName.map(Object::toString).orElse("")+methods; }
  }
  record TypedLiteral(T.RCC t,Optional<Literal> l,Pos pos) implements E{
    public TypedLiteral{ assert nonNull(t,l); }
    public <R> R accept(EVisitor<R> v){ return v.visitTypedLiteral(this); }
    public String toString(){ return "TypedLiteral"+t+l.map(Object::toString).orElse(""); }
  }
  record DeclarationLiteral(Optional<RC> rc, Declaration dec) implements E{
    public DeclarationLiteral{ assert nonNull(rc,dec); }
    public <R> R accept(EVisitor<R> v){ return v.visitDeclarationLiteral(this); }
    public Pos pos(){ return dec.pos(); }
    public String toString(){ return "DeclarationLiteral"+rc.map(Object::toString).orElse("")+dec; }
  }
  //if pat is present, this is an x=e posts, if absent this is a normal meth call.
  record CallSquare(Optional<RC> rc, List<T> ts){
    public CallSquare{ assert nonNull(rc) && unmodifiable(ts, "E.Call.targs"); }
  }
  record Call(E e, MName name, Optional<CallSquare> targs, boolean pars, Optional<XPat> pat, List<E> es, Pos pos) implements E{
    public Call{
      assert nonNull(e,name,targs,pat);
      assert unmodifiable(es, "E.Call.es");
      assert pat.isPresent() || eq(es.size(),name.arity(),"Call arity");
      assert pars || es.size() < 2;
      assert validOpt(pat,_->eq(es.size(),1,"invalid equal sugar"));
      assert validOpt(pat,_->eq(name.arity(),2,"invalid equal sugar"));
    }
    public <R> R accept(EVisitor<R> v){ return v.visitCall(this); }
    public String toString(){ return "Call["+e+"]"+name
      +targs.map(Object::toString).orElse("")
      +pars+pat.map(Object::toString).orElse("")+es; }
  }
  record StringInter(boolean simple, Optional<E> e, List<Integer> hashCounts, List<String> strings, List<E> es,Pos pos) implements E{
    public StringInter{
      assert nonNull(e);
      assert unmodifiable(hashCounts,"string # counts");
      assert unmodifiable(strings,"string parts");
      assert unmodifiable(es,"string es");
      assert eq(strings.size(),es.size()+1,"string interpolation");
    }
    public <R> R accept(EVisitor<R> v){ return v.visitStringInter(this); }
    public String toString(){ return
      e.map(Object::toString).orElse("")
      +"Inter["+simple+"]"
      +hashCounts+strings.stream().map(s->s.replace("\n","\\n")).toList()+es;
    }
  }
  record Implicit(Pos pos) implements E{ 
    public <R> R accept(EVisitor<R> v){ return v.visitImplicit(this); }
    public String toString(){ return "::"; }
  }
}