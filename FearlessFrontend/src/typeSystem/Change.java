package typeSystem;

import static fearlessParser.RC.imm;
import static fearlessParser.RC.read;

import core.*;
import core.E.*;
//intentionally merging "set to read" vs "weakened to read"
public sealed interface Change{
  sealed interface WithT extends Change{ T currentT(); }
  static Change keepStrengthenToImm(Literal l, M m, WithT tail){
    var newT= tail.currentT().withRC(imm);
    if (newT.equals(tail.currentT())){ return tail; }
    return new KeepStrengthenToImm(l,m,newT,tail);
  }
  static Change keepSetToRead(Literal l, M m, WithT tail){
    var newT= tail.currentT().withRC(read);
    if (newT.equals(tail.currentT())){ return tail; }
    return new KeepSetToRead(l,m,newT,tail);
  }
  static Change keepSetToReadImm(Literal l, M m, WithT tail){
    var newT= tail.currentT().readImm();
    if (newT.equals(tail.currentT())){ return tail; }
    return new KeepSetToReadImm(l,m,newT,tail);
  }
  static Change dropMutInImm(Literal l,T atDrop){
    return new DropMutInImm(l,atDrop);
  }
  static Change dropReadHMutH(Literal l, T atDrop){
    return new DropReadHMutH(l,atDrop);
  }
  static Change dropFTV(Literal l, T atDrop){
    return new DropFTV(l,atDrop);
  }      
  record Same(T currentT) implements WithT{}
  record KeepStrengthenToImm(Literal l, M m, T currentT, WithT tail) implements WithT{}
  record KeepSetToRead(Literal l, M m, T currentT, WithT tail) implements WithT{}
  record KeepSetToReadImm(Literal l, M m, T currentT, WithT tail) implements WithT{}
  sealed interface NoT extends Change{}
  record DropMutInImm(Literal l, T atDrop)implements NoT{}
  record DropReadHMutH(Literal l, T atDrop)implements NoT{}
  record DropFTV(Literal l, T atDrop)implements NoT{}
}