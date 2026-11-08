package fuzz;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.StringEntry;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import core.FearlessException;
import fearlessParser.Parse;
import tools.SourceOracle;

final class Seeds{
  static final List<String> all= fromTestClasses();
  static final List<String> annotated= all.stream().filter(Mutations::annotated).filter(Seeds::parses).toList();
  static List<String> fromTestClasses(){
    try (var files= Files.walk(testClasses())){
      return files.filter(p -> p.toString().endsWith(".class"))
        .flatMap(Seeds::strings).filter(Seeds::isProgram).distinct().sorted().toList();
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
  }
  static Path testClasses(){
    try{ return Path.of(Seeds.class.getProtectionDomain().getCodeSource().getLocation().toURI()); }
    catch (URISyntaxException e){ throw new IllegalStateException(e); }
  }
  static Stream<String> strings(Path classFile){
    var res= new ArrayList<String>();
    try{ for (var e : ClassFile.of().parse(classFile).constantPool()){ if (e instanceof StringEntry s){ res.add(s.stringValue()); } } }
    catch (IOException e){ throw new UncheckedIOException(e); }
    return res.stream();
  }
  static boolean isProgram(String s){
    return s.contains("\n") && !s.contains("|") && !s.contains("Error") && (s.contains("->") || s.contains(":{"));
  }
  static boolean parses(String s){
    try{ Parse.from(SourceOracle.defaultDbgFearPath(0), s); return true; }
    catch (FearlessException _){ return false; }
  }
}
