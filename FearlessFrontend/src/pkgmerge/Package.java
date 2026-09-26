package pkgmerge;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import core.T;
import fearlessFullGrammar.Declaration;
import inference.E;
import message.WellFormednessErrors;
import utils.Join;

public record Package(String name, Map<String,String> map, List<Declaration> decs, DeclaredNames names, Logger log){
  public WellFormednessErrors err(){ return new WellFormednessErrors(name); }
  public record Logger(boolean active, ArrayList<String> logs){
    public void logInferenceDeclaration(E.Literal d, List<T.C> cs){
      if (!active){ return; }
      logs.add(d.name().s()+Join.of(d.bs(),"[",", ","]","")+":"+Join.of(cs,"",", ","","")+"{'"+d.thisName()+Join.of(d.ms(),"","","","")+"}");
    }
  }
  public static Logger onLogger(){ return new Logger(true,new ArrayList<>()); }
  public static Logger offLogger(){ return new Logger(false,null); }
}