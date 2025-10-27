package fullWellFormedness;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import fearlessFullGrammar.TName;
import inferenceGrammar.Declaration;
import message.WellFormednessErrors;

public class ToInference {
  List<Declaration> of(Package p, OtherPackages other, FreshPrefix fresh){
    Function<TName,TName> f= tn->{
      var pN= tn.pkgName();
      if (!pN.isEmpty()){
        var mPN= p.map().get(pN);
        if (mPN == null){ return tn; }
        return tn.withOverridePkgName(mPN);
      }
      if (numStr(tn)){ return tn.withPkgName("base"); }
      var mapped= p.map().get(tn.s());
      if (mapped != null){ return new TName(mapped,tn.arity(),tn.pos()); } //if mapped is not defined with any arity
      var defined= p.names().decNames().stream().anyMatch(tni->tni.equals(tn));//this also checks arity
      if (defined){ return tn.withPkgName(p.name()); }
      throw WellFormednessErrors.usedUndeclaredName(tn,p);
      //here, we know it is not defined (either at all or with the right arity)
    };
    //TODO: if an use does not correspond to a defName in the other package, we should get an error here
    ArrayList<Declaration> decs= new ArrayList<>();
    var v= new InjectionToInferenceVisitor(new ArrayList<>(),new ArrayList<>(),f,decs,p,new ArrayList<>(),other,fresh);
    p.decs().forEach(di->v.addDeclaration(di,true));
    return List.copyOf(decs);
  }
  boolean numStr(TName n){ return "+-1234567890\"\'".contains(n.s().substring(0,1)); }
}