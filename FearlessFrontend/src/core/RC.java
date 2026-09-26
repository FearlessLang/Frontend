package core;

import java.util.List;

import utils.OneOr;

public enum RC{
  imm, mut, read, iso, mutH, readH;
  public boolean isSubType(RC other){ //this <= other
    if (this == other){ return true; }
    if (other == readH){ return true; }
    return switch (this){
      case mut -> other == mutH || other == read;
      case imm -> other == read;
      case iso -> true;
      case readH, read, mutH -> false;
    };
  }
  public boolean isH(){ return this == mutH || this == readH; }
  public boolean isReadOrImm(){ return this == read || this == imm; }
  public boolean isIsoOrImm(){ return this == iso || this == imm; }
  public RC isoToMut(){ return this == iso? mut : this; }
  public RC readImm(){ return isIsoOrImm() ? imm : read; }
  public static B get(List<B> bs, String name){
    return OneOr.of("Type variable not found",bs.stream().filter(b->b.x().equals(name)));
  }
  public String toStrSpace(){ return toStrSpace(true); }
  public String toStrSpace(boolean skipImm){ return this == imm && skipImm?"":this+" "; }
}