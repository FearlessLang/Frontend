package fuzz;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;

import org.junit.jupiter.api.Test;

import core.AllLs;
import tools.SourceOracle;

public final class LibraryTest extends testUtils.FearlessTestBase{
  static final Path root= Path.of(System.getProperty("standardLibrary"));
  static final int mutantsPerProject= 10;
  @Test void standardLibrary(){
    var base= oracle(root.resolve("base"));
    var full= compileAll("base", base, otherFrom(List.of()));
    var compactBase= checkCompact ? compactAll("base", base, List.of()) : List.<compact.Frontend.Literal>of();
    var compactOther= compactBase.stream().flatMap(LibraryTest::compactAllLs).toList();
    var fuzz= new Fuzz("standardLibrary", otherFrom(List.of()).mergeWith(AllLs.of(full), -1), compactOther, base);
    if (checkCompact){ differentDeclarations(fuzz, canon(lines(full)), canon(compact.Print.lines(compactBase))); }
    var packages= new ArrayList<Fuzz.Package>();
    for (var project : projects()){
      var name= project.getFileName().toString().substring(1);
      var shown= project.getParent().getFileName().toString();
      var files= files(project);
      packages.add(new Fuzz.Package(name, oracle(files), shown));
      var paths= new ArrayList<>(files.keySet());
      var rnd= new Random(shown.hashCode());
      for (int i= 0; i < mutantsPerProject; i += 1){
        var path= paths.get(rnd.nextInt(paths.size()));
        var mutant= new TreeMap<>(files);
        mutant.put(path, Mutations.underAnnotate(files.get(path), rnd, Mutations.inferable));
        packages.add(new Fuzz.Package(name, oracle(mutant), shown+", with "+path+" written as\n"+mutant.get(path)));
      }
    }
    fuzz.checkPackages(packages);
    fuzz.assertNothingFound();
  }
  static void differentDeclarations(Fuzz fuzz, String full, String compact){
    var fs= List.of(full.split("\n"));
    var cs= List.of(compact.split("\n"));
    for (var f : fs){
      var c= cs.stream().filter(l -> key(l).equals(key(f))).findFirst().orElse("");
      if (!c.equals(f)){ fuzz.found("C: base, the full core has "+Fuzz.firstDifference(f, c), "full:    "+f+"\ncompact: "+c); }
    }
  }
  static String key(String declaration){
    var colon= declaration.indexOf(':');
    var open= declaration.indexOf('[');
    return open < 0 || open > colon ? declaration.substring(0, colon) : declaration.substring(0, declaration.indexOf("]:")+1);
  }
  static List<Path> projects(){
    try (var all= Files.list(root.resolve("integrationTests"))){
      return all.filter(Files::isDirectory).sorted().map(LibraryTest::packages).filter(ps -> ps.size() == 1).map(List::getFirst).toList();
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
  }
  static List<Path> packages(Path project){
    try (var ps= Files.list(project)){ return ps.filter(p -> Files.isDirectory(p) && p.getFileName().toString().startsWith("_")).toList(); }
    catch (IOException e){ throw new UncheckedIOException(e); }
  }
  static SourceOracle oracle(Path folder){ return oracle(files(folder)); }
  static SourceOracle oracle(TreeMap<String,String> files){
    var b= SourceOracle.debugBuilder();
    for (var e : files.entrySet()){ b= b.putURI(URI.create(e.getKey()), e.getValue()); }
    return b.build();
  }
  static TreeMap<String,String> files(Path folder){
    var res= new TreeMap<String,String>();
    try (var fs= Files.walk(folder)){
      for (var f : fs.filter(p -> p.toString().endsWith(".fear")).toList()){
        res.put("fear:/"+folder.getFileName()+"/"+folder.relativize(f).toString().replace('\\', '/'), Files.readString(f).replace("\r", ""));
      }
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
    return res;
  }
}
