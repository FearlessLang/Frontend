package core;

import java.util.Map;

import message.CompactPrinter;
import message.Err;
import message.TypeNamePrinter;

public record ExportedToStr(String pkgName, Map<String,String> uses){
  public String typeName(TName n){ return new TypeNamePrinter(pkgName, uses, _ -> {}).of(n); }
  public String typeNameWithArity(TName n){ return typeName(n)+Err.genArity(n.arity()); }
  public String typeName(T.C c){ return type(new T.RCC(RC.imm, c, c.span())); }
  public String type(T t){ return new CompactPrinter(pkgName, uses, _ -> {}).msgT(t); }
}
