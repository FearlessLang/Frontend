package fuzz;

import java.util.List;

import fuzz.Gen.OneOf;
import fuzz.Gen.Size;
import fuzz.Gen.Weight;

interface Ast{
  enum Rc{ none, imm, read, mut, iso }
  enum Nth{ first, second, third }
  record Program(Dec a, Dec b, Dec c){}
  enum Supers{ none, first, second, both }
  record Dec(Supers supertypes, @Size(max=1) List<@OneOf({"Box[A]", "Box[B]"}) String> boxes, @Size(max=3) List<Meth> methods){}
  record Meth(Rc rc, boolean typed, boolean generic, @Size(max=2) List<Ty> parameters, Ty result, Body body){}
  sealed interface Body{}
  record Abstract() implements Body{}
  @Weight(3) record Returns(E e) implements Body{}
  sealed interface Ty{}
  @Weight(4) record Named(Rc rc, @OneOf({"A", "B", "C", "base.Void", "Box[A]", "Box[B]", "Self", "Self", "X"}) String name) implements Ty{}
  record Lambda(Rc rc, @Size(max=2) List<Named> arguments, Named result) implements Ty{}
  sealed interface E{}
  record This() implements E{}
  record Parameter(Nth nth) implements E{}
  record TypeName(@OneOf({"A", "B", "C", "base.Void", "Id"}) String name) implements E{}
  record Call(E receiver, Nth method, Rc rc, @Size(max=2) List<E> arguments) implements E{}
  record Literal(Rc rc, @OneOf({"", "A", "B", "C", "Box[A]", "Box[B]"}) String head, boolean selfName, @Size(max=2) List<Meth> methods) implements E{}
  record Declared(Rc rc, @OneOf({"", "A", "B", "C"}) String supertype, @Size(max=2) List<Meth> methods) implements E{}
  record Function(@Size(max=2) List<Nth> parameters, E body) implements E{}
}
