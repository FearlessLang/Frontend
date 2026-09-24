package core;

import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import core.E.Literal;
import message.CompactPrinter;
import message.TypeNamePrinter;

public record ExportedToStr(String pkgName, Map<String,String> uses){
  private CompactPrinter printer(){ return new CompactPrinter(pkgName,uses,false); }
  private TypeNamePrinter names(){ return new TypeNamePrinter(false,pkgName,uses); }
  public String expr(E e){ return printer().limit(e,220); }
  public String sig(Sig s){ return printer().sig(s).stripLeading(); }
  public String lit(Literal l){ return expr(l); }
  public String typeName(TName n){ return names().ofFull(n); }
  public String typeNameWithArity(TName n){
    var base= typeName(n);
    if (n.arity() == 0){ return base; }
    return base+"["+IntStream.range(0,n.arity()).mapToObj(_->"_").collect(Collectors.joining(","))+"]";
  }  
  public String typeName(T.C c){
    if (c.ts().isEmpty()){ return typeNameWithArity(c.name()); }
    return typeName(c.name())+"["+c.ts().stream().map(this::type).collect(Collectors.joining(","))+"]";
  }
  public String type(T t){ return switch (t){
    case T.X x -> x.name();
    case T.RCX x -> x.rc()+" "+x.x().name();
    case T.ReadImmX x -> "read/imm "+x.x().name();
    case T.RCC r -> r.rc().toStrSpace()+typeName(r.c());
  };}
}
