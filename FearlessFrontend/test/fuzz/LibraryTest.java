package fuzz;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;

import core.AllLs;
import tools.SourceOracle;

public final class LibraryTest extends testUtils.FearlessTestBase{
  static final Path root= Path.of(System.getProperty("standardLibrary"));
  @Test void standardLibrary(){
    var base= oracle(root.resolve("base"));
    var full= compileAll("base", base, otherFrom(List.of()));
    var compactBase= checkCompact ? compactAll("base", base, List.of()) : List.<compact.Frontend.Literal>of();
    var compactOther= compactBase.stream().flatMap(LibraryTest::compactAllLs).toList();
    var fuzz= new Fuzz("standardLibrary", otherFrom(List.of()).mergeWith(AllLs.of(full), -1), compactOther, base);
    if (checkCompact){ differentDeclarations(fuzz, canon(lines(full)), canon(compact.Print.lines(compactBase))); }
    for (var project : projects()){ fuzz.checkPackage(project.getFileName().toString().substring(1), oracle(project), project.getParent().getFileName().toString()); }
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
  static SourceOracle oracle(Path folder){
    var b= SourceOracle.debugBuilder();
    try (var fs= Files.walk(folder)){
      for (var f : fs.filter(p -> p.toString().endsWith(".fear")).sorted().toList()){
        b= b.putURI(URI.create("fear:/"+folder.getFileName()+"/"+folder.relativize(f).toString().replace('\\', '/')), Files.readString(f).replace("\r", ""));
      }
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
    return b.build();
  }
}
