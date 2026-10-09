package core;

import java.util.Map;

import core.E.Literal;
import message.CompactPrinter;
import message.Err;
import message.TypeNamePrinter;
import utils.Join;

public record ExportedToStr(String pkgName, Map<String,String> uses){
  private CompactPrinter printer(){ return new CompactPrinter(pkgName,uses,_->{},false); }
  public String expr(E e){ return printer().limit(e,220); }
  public String lit(Literal l){ return expr(l); }
  public String sig(Sig s){ return printer().sig(s).stripLeading(); }
  public String typeName(TName n){ return new TypeNamePrinter(false,pkgName,uses,_->{}).ofFull(n); }
  public String typeNameWithArity(TName n){ return typeName(n)+Err.genArity(n.arity()); }
  public String typeName(T.C c){
    return typeName(c.name())+Join.of(c.ts().stream().map(this::type),"[",",","]","");
  }
  public String type(T t){ return printer().msgT(t); }
}
