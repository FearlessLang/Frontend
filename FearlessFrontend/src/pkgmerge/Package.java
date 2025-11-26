package pkgmerge;

import java.util.Map;
import java.util.stream.Collectors;

import core.T;

import java.util.ArrayList;
import java.util.List;

import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull.Role;
import inference.E;

public record Package(String name, Role role, Map<String,String> map, List<Declaration> decs, DeclaredNames names, Logger log){
  public record Logger(boolean active, ArrayList<String> logs){
    public void logInferenceDeclaration(E.Literal d, List<T.C> cs) {
      if (!active){ return; }
      var bsS= d.bs().isEmpty()?"":"["+d.bs().stream().map(Object::toString).collect(Collectors.joining(", "))+"]";
      var csS= cs.stream().map(Object::toString).collect(Collectors.joining(", "));
      var msS= d.ms().stream().map(Object::toString).collect(Collectors.joining(""));
      var decTest= d.name().s()+bsS+":"+csS+"{'"+d.thisName()+msS+"}";
      logs.add(decTest);
    } 
  }
  public static Logger logger(){ return new Logger(true,new ArrayList<>()); }//TODO: this can be configured when more mature
}