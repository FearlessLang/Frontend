package fullWellFormedness;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.function.Function;

import fearlessFullGrammar.TName;
import inferenceGrammar.Declaration;

public class ToInference {
  ArrayList<Declaration> of(Package p, HashMap<String,String> map){
    Function<TName,TName> f= tn->{
      var mapped= map.get(tn.s());
      if (mapped != null){ return new TName(mapped,tn.arity(),tn.asUStrLit(),tn.pos()); } //if mapped is not defined with any arity
      var defined= p.names().decNames().stream().anyMatch(tni->tni.equals(tn));//this also checks arity
      if (defined){ return new TName(p.name()+"."+tn.s(),tn.arity(),tn.asUStrLit(),tn.pos()); }
      //here, we know it is not defined (either at all or with the right arity)
      throw WellFormednessErrors.usedUndeclaredName(tn,p);
    };
    //TODO: if an use does not correspond to a defName in the other package, we should get an error here
    ArrayList<Declaration> decs= new ArrayList<>();
    var v= new InjectionToInferenceVisitor(new ArrayList<>(),f,decs,p,new ArrayList<>(),new FreshPrefix(p));
    p.decs().forEach(di->v.addDeclaration(di,true));
    return decs;
  }
}