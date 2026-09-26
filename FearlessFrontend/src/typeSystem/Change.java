package typeSystem;

import static core.RC.*;

import java.util.function.Function;

import core.*;
import core.E.*;
//intentionally merging "set to read" vs "weakened to read"
public sealed interface Change{
  sealed interface WithT extends Change{ T currentT(); }
  private static Change tailOr(WithT tail, T newT, Function<T,Change> make){ return newT.equals(tail.currentT()) ? tail : make.apply(newT); }
  static Change keepStrengthenToImm(Literal l, M m, WithT tail){ return tailOr(tail, tail.currentT().withRC(imm), t->new KeepStrengthenToImm(l,m,t,tail)); }
  static Change keepSetToRead(Literal l, M m, WithT tail){ return tailOr(tail, tail.currentT().withRC(read), t->new KeepSetToRead(l,m,t,tail)); }
  static Change keepSetToReadImm(Literal l, M m, WithT tail){ return tailOr(tail, tail.currentT().readImm(), t->new KeepSetToReadImm(l,m,t,tail)); }
  record Same(T currentT) implements WithT{}
  record KeepStrengthenToImm(Literal l, M m, T currentT, WithT tail) implements WithT{}
  record KeepSetToRead(Literal l, M m, T currentT, WithT tail) implements WithT{}
  record KeepSetToReadImm(Literal l, M m, T currentT, WithT tail) implements WithT{}
  sealed interface NoT extends Change{ Literal l(); T atDrop(); }
  record DropMutInImm(Literal l, T atDrop)implements NoT{}
  record DropReadHMutH(Literal l, T atDrop)implements NoT{}
  record DropFTV(Literal l, T atDrop)implements NoT{}
  record CapFree(Literal l, T atDrop)implements NoT{}

}