package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.ChildJvm;
import tools.Fs;
import tools.JavacTool;
import tools.PathClassLoader;
import utils.Err;
import utils.Push;

final class PathClassLoaderTest{
  @TempDir static Path tmp;
  static Path odd;
  static Path plain;
  @BeforeAll static void jars(){
    odd= NotUnicode.in(tmp);
    plain= tmp.resolve("plain");
    Fs.ofV(() -> Files.createDirectories(odd));
    Fs.ofV(() -> Files.createDirectories(plain));
    var src= tmp.resolve("src");
    Fs.writeUtf8(src.resolve("Probe.java"), """
      import java.util.Collections;
      public class Probe{ public static void main(String[] a) throws Exception{
        var l= Probe.class.getClassLoader();
        var url= l.getResource("data.txt");
        System.out.print(l.getClass().getName()+" "+(Thread.currentThread().getContextClassLoader() == l)+" "+url.getProtocol()+"\\n");
        System.out.print(new String(url.openStream().readAllBytes()).trim()+" "+new String(Probe.class.getResourceAsStream("/data.txt").readAllBytes()).trim()+"\\n");
        System.out.print(Collections.list(l.getResources("data.txt")).size()+" "+Lib.name()+" "+String.join(",", a)+" "+System.getProperty("sun.jnu.encoding")+"\\n");
      } }
      """);
    Fs.writeUtf8(src.resolve("Lib.java"), "public class Lib{ public static String name(){ return \"lib\"; } }\n");
    var probe= tmp.resolve("probe");
    var lib= tmp.resolve("lib");
    Fs.runTool("javac", List.of("-d", lib.toString(), src.resolve("Lib.java").toString()));
    Fs.runTool("javac", List.of("-d", probe.toString(), "-cp", lib.toString(), src.resolve("Probe.java").toString()));
    Fs.writeUtf8(probe.resolve("data.txt"), "odd\n");
    Fs.writeUtf8(lib.resolve("data.txt"), "plain\n");
    JavacTool.jar(probe, tmp.resolve("a.jar"));
    JavacTool.jar(lib, tmp.resolve("b.jar"));
    Fs.ofV(() -> Files.copy(tmp.resolve("a.jar"), odd.resolve("a.jar")));
    Fs.ofV(() -> Files.copy(tmp.resolve("b.jar"), plain.resolve("b.jar")));
  }
  static String run(Map<String,String> env, List<String> args) throws InterruptedException{
    var out= new StringBuilder();
    var jvm= ChildJvm.start(args, env, out::append);
    jvm.await();
    return out.toString();
  }
  static String probe(Map<String,String> env) throws InterruptedException{
    return run(env, Push.<String>of(PathClassLoader.codeArgs(List.of(odd, plain)), List.of("-cp", PathClassLoader.jar().toString(), PathClassLoader.class.getName(), "Probe", "x", "y")));
  }
  @Test void aPathReadsBackFromItsText(){
    var back= PathClassLoader.pathOf(PathClassLoader.argOf(odd.resolve("a.jar")));
    assertEquals(odd.resolve("a.jar"), back);
    assertTrue(Files.isRegularFile(back));
  }
  @Test void theLoaderReadsJarsInAFolderWhoseNameIsNotUnicode() throws InterruptedException{
    Err.strCmp("""
      tools.PathClassLoader true fearless
      odd odd
      2 lib x,y [###]
      """, probe(Map.of("LC_ALL", "C.UTF-8")));
  }
  @Test void theLoaderReadsJarsInAFolderWhoseNameIsNotAscii() throws InterruptedException{
    Err.strCmp("""
      tools.PathClassLoader true fearless
      odd odd
      2 lib x,y [###]
      """, probe(Map.of("LC_ALL", "C")));
  }
  @Test void theSystemLoaderDoesNotReadAJarInAFolderWhoseNameIsNotUnicode() throws InterruptedException{
    Err.strCmp("Error: Could not find or load main class Probe[###]",
      run(Map.of("LC_ALL", "C.UTF-8"), List.of("-cp", odd.resolve("a.jar")+File.pathSeparator+plain.resolve("b.jar"), "Probe")));
  }
}
