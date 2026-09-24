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
    if (c.ts().isEmpty()){ return typeNameWithArity(c.name()); }
    return typeName(c.name())+Join.of(c.ts().stream().map(this::type),"[",",","]");
  }
  public String type(T t){ return switch (t){
    case T.X x -> x.name();
    case T.RCX x -> x.rc()+" "+x.x().name();
    case T.ReadImmX x -> "read/imm "+x.x().name();
    case T.RCC r -> r.rc().toStrSpace()+typeName(r.c());
  };}
}
