package core;

import java.util.Map;

import core.E.Literal;
import message.CompactPrinter;
import message.Err;
import message.TypeNamePrinter;
import utils.Join;

public record ExportedToStr(String pkgName, Map<String,String> uses){
  private CompactPrinter printer(){ return new CompactPrinter(pkgName,uses,false); }
  private TypeNamePrinter names(){ return new TypeNamePrinter(false,pkgName,uses); }
  public String expr(E e){ return printer().limit(e,220); }
  public String sig(Sig s){ return printer().sig(s).stripLeading(); }
  public String lit(Literal l){ return expr(l); }
  public String typeName(TName n){ return names().ofFull(n); }
  public String typeNameWithArity(TName n){ return typeName(n)+Err.genArity(n.arity()); }
  public String typeName(T.C c){
    return typeName(c.name())+Join.of(c.ts().stream().map(this::type),"[",",","]","");
  }
  public String type(T t){ return switch (t){
    case T.X(var name, _) -> name;
    case T.RCX(var rc, var x) -> rc+" "+x.name();
    case T.ReadImmX(var x) -> "read/imm "+x.name();
    case T.RCC(var rc, var c, _) -> rc.toStrSpace()+typeName(c);
  };}
}
