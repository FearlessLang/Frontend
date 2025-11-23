package toInfer;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Stream;

import fearlessFullGrammar.TName;
import fearlessParser.RC;
import fearlessParser.TokenKind;
import inference.E;
import inject.Methods;
import message.FearlessException;
import message.WellFormednessErrors;
import naming.FreshPrefix;
import optimizedTypes.LiteralDeclarations;
import pkgmerge.OtherPackages;
import pkgmerge.Package;

public class ToInference{
  private TName fCurrent(Package p, TName simple, TName full, boolean withPkg, OtherPackages other){
    var defined= p.names().decNames().stream()
      .anyMatch(tni->tni.equals(simple)); //this also checks arity
    if (defined){ return full; } //here, we know it is not defined (either at all or with the right arity)
    throw undeclaredType(withPkg?full:simple,p.name(),p,other);
    }
  private FearlessException undeclaredType(TName tn, String contextPkg, Package p, OtherPackages other){
    var otherTypes= other.dom();
    var declared= p.names().decNames();
    var imported= p.map().entrySet().stream()
      .filter(e->TokenKind.validate(e.getKey(), TokenKind.UppercaseId))//TODO: check how the map is created. Is it really just Uppercase + lowercase as two disjoint options?
      .flatMap(e->otherTypes.stream()
        .filter(t->t.s().equals(e.getValue()))
        .map(t->new TName(p.name()+"."+e.getKey(), t.arity(),t.pos()))
      ).toList();
    var scope= Stream.concat(declared.stream(), imported.stream()).toList();
    var all= Stream.concat(declared.stream(), otherTypes.stream()).toList();
    return WellFormednessErrors.usedUndeclaredName(tn, contextPkg, scope, all);
  }
  public List<E.Literal> of(Package p, Methods meths, OtherPackages other, FreshPrefix fresh){
    Function<TName,TName> f= tn->{
      var pN= tn.pkgName();
      if (pN.isEmpty()){
        if (LiteralDeclarations.isPrimitiveLiteral(tn.s())){ return tn.withPkgName("base"); }
        var mapped= p.map().get(tn.s());
        if (mapped != null){
          var res= new TName(mapped,tn.arity(),tn.pos());
          var ok= other.dom().stream().anyMatch(t->t.equals(res));
          if (!ok){ throw undeclaredType(tn,res.pkgName(),p,other); }
          return res;
        }
        return fCurrent(p,tn,tn.withPkgName(p.name()),false,other);
      }
      var mPN= p.map().get(pN);
      var pkg= mPN == null ? pN : mPN;
      if (mPN != null){ tn = tn.withOverridePkgName(mPN); }
      if (pkg.equals(p.name())){ return fCurrent(p,tn.withoutPkgName(),tn,true,other); }
      if (other.of(tn) != null){ return tn; }
      var lit= pkg.equals("base") && LiteralDeclarations.isPrimitiveLiteral(tn.simpleName());        
      if (lit){ return tn; }
      throw undeclaredType(tn,p.name(),p,other);
    };
    ArrayList<E.Literal> decs= new ArrayList<>();
    var v= new InjectionToInferenceVisitor(meths, new ArrayList<>(),new ArrayList<>(),f,decs,p,new ArrayList<>(),other,fresh);
    p.decs().forEach(di->v.addDeclaration(RC.imm,di,true));
    return List.copyOf(decs);
  }
}