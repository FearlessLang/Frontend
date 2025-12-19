package pkgmerge;

import java.util.Map;

import core.T;

import java.util.ArrayList;
import java.util.List;

import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull.Role;
import inference.E;
import message.Join;
import message.WellFormednessErrors;

public record Package(String name, Role role, Map<String,String> map, List<Declaration> decs, DeclaredNames names, Logger log){
  public WellFormednessErrors err(){ return new WellFormednessErrors(name); }
  public record Logger(boolean active, ArrayList<String> logs){
    public void logInferenceDeclaration(E.Literal d, List<T.C> cs) {
      if (!active){ return; }
      var bsS= Join.of(d.bs(),"[",", ","]","");
      var csS= Join.of(cs,"",", ","","");
      var msS= Join.of(d.ms(),"","","","");
      var decTest= d.name().s()+bsS+":"+csS+"{'"+d.thisName()+msS+"}";
      logs.add(decTest);
    } 
  }
  public static Logger onLogger(){ return new Logger(true,new ArrayList<>()); }
  public static Logger offLogger(){ return new Logger(false,null); }
}