package fearlessFullGrammar;

import java.util.*;

import core.MName;
import core.RC;
import core.TSpan;
import utils.Pos;

import static fearlessParser.TokenKind.*;
import static offensiveUtils.Require.*;

public sealed interface E extends core.Src.SrcObj{
  Pos pos();
  TSpan span();
  <R> R accept(EVisitor<R> v);
  record X(String name, Pos pos) implements E{
    public X{ assert validate(name, "parameter name",LowercaseId,Underscore); }
    public <R> R accept(EVisitor<R> v){ return v.visitX(this); }
    public String toString(){ return name; }
    public TSpan span(){ return TSpan.fromPos(pos,name.length()); }
  }
  record Round(E e) implements E{
    public Round{ assert nonNull(e); }
    public Pos pos(){ return e.pos(); }
    public <R> R accept(EVisitor<R> v){ return v.visitRound(this); }
    public String toString(){ return "("+e+")"; }
    public TSpan span(){ return e.span(); }
  }
  record Literal(Optional<E.X> thisName, List<M> methods, TSpan span) implements E, Comparable<Literal>{
    public Literal{
      assert unmodifiableDistinct(methods, "L.Full.methods");
      assert nonNull(thisName,span);
    }
    public Pos pos(){ return span.pos(); }
    public <R> R accept(EVisitor<R> v){ return v.visitLiteral(this); }
    public String toString(){ return "Literal"+thisName.map(Object::toString).orElse("")+methods; }
    public Literal withSpan(TSpan span){ return new Literal(thisName,methods,span); }
    @Override public int compareTo(Literal o){ return span().inner.compareTo(o.span().inner); }
  }
  record TypedLiteral(T.RCC t, Optional<Literal> l,Pos pos) implements E{
    public TypedLiteral{ assert nonNull(t,l,pos); }
    public <R> R accept(EVisitor<R> v){ return v.visitTypedLiteral(this); }
    public String toString(){ return "TypedLiteral"+t+l.map(Object::toString).orElse(""); }
    public TSpan span(){ return TSpan.fromPos(pos,t.c().name().s().length()); }
  }
  record DeclarationLiteral(Optional<RC> rc, Declaration dec) implements E{
    public DeclarationLiteral{ assert nonNull(rc,dec); }
    public <R> R accept(EVisitor<R> v){ return v.visitDeclarationLiteral(this); }
    public Pos pos(){ return dec.pos(); }
    public TSpan span(){ return dec.span(); }
    public String toString(){ return "DeclarationLiteral"+rc.map(Object::toString).orElse("")+dec; }
  }
  //if pat is present, this is an x=e posts, if absent this is a normal meth call.
  record CallSquare(Optional<RC> rc, List<T> ts, Pos endPos){
    public CallSquare{ assert nonNull(rc) && unmodifiable(ts, "E.Call.targs"); }
    public String toString(){ return "CallSquare[rc="+rc+",ts="+ts+"]"; }
  }
  record Call(E e, MName name, Optional<CallSquare> targs, boolean pars, Optional<XPat> pat, List<E> es, Pos pos) implements E{
    public Call{
      assert nonNull(e,name,targs,pat,pos);
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
    public TSpan span(){
      if (!es.isEmpty()){ return TSpan.merge(e.span(),es.getLast().span()); }
      if (targs.isEmpty()){ return TSpan.merge(e.span(),TSpan.fromPos(pos,name.s().length())); } 
      return TSpan.merge(e.span(),TSpan.fromPos(targs.get().endPos()));      
    }
  }
  record StringInter(boolean simple, Optional<E> e, List<Integer> hashCounts, List<String> strings, List<E> es, TSpan span) implements E{
    public StringInter{
      assert nonNull(e,span);
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
    public Pos pos(){ return span.pos(); }
  }
  record Implicit(Pos pos) implements E{ 
    public <R> R accept(EVisitor<R> v){ return v.visitImplicit(this); }
    public String toString(){ return "::"; }
    public TSpan span(){ return TSpan.fromPos(pos,2); }
  }
}