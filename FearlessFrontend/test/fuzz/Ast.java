package fuzz;

import java.util.List;

import fuzz.Gen.OneOf;
import fuzz.Gen.Size;
import fuzz.Gen.Weight;

interface Ast{
  enum Rc{ none, imm, read, mut, iso, readH, mutH }
  enum Nth{ first, second, third, fourth }
  record Program(Dec a, Dec b, Dec c, Dec d){}
  record Dec(@Size(max=2) List<Nth> supertypes, @Size(max=1) List<@OneOf({"Box[A]", "Box[B]", "Box[Self]"}) String> boxes, @Size(max=4) List<Meth> methods){}
  record Meth(Rc rc, boolean typed, boolean generic, @Size(max=3) List<Ty> parameters, Ty result, Body body){}
  sealed interface Body{}
  record Abstract() implements Body{}
  @Weight(3) record Returns(E e) implements Body{}
  sealed interface Ty{}
  @Weight(4) record Named(Rc rc, @OneOf({"A", "B", "C", "D", "base.Void", "Box[A]", "Box[B]", "Box[Self]", "Self", "Self", "X", "base.Bool", "base.Nat", "Box[Box[A]]"}) String name) implements Ty{}
  record Lambda(Rc rc, @Size(max=2) List<Named> arguments, Named result) implements Ty{}
  sealed interface E{}
  record This() implements E{}
  record Parameter(Nth nth) implements E{}
  record TypeName(@OneOf({"A", "B", "C", "D", "base.Void", "Id", "base.True", "base.False", "5"}) String name) implements E{}
  record Call(E receiver, Nth method, Rc rc, @Size(max=1) List<Named> typeArguments, @Size(max=2) List<E> arguments) implements E{}
  record Literal(Rc rc, @OneOf({"", "A", "B", "C", "D", "Box[A]", "Box[B]"}) String head, boolean selfName, @Size(max=2) List<Meth> methods) implements E{}
  record Declared(Rc rc, @OneOf({"", "A", "B", "C", "D"}) String supertype, @Size(max=2) List<Meth> methods) implements E{}
  record Function(@Size(max=2) List<Nth> parameters, E body) implements E{}
}
