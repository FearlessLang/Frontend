package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

import java.nio.file.Path;
import java.util.List;
import java.util.stream.Stream;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.ChildJvm;
import tools.Fs;
import utils.Err;

final class ChildJvmTest{
  @TempDir static Path classes;
  @BeforeAll static void compileSpam(){
    var src= classes.resolve("Spam.java");
    Fs.writeUtf8(src, "public class Spam{ public static void main(String[] a){ while (true){ System.out.println(\"spam\"); } } }\n");
    var probe= classes.resolve("Probe.java");
    Fs.writeUtf8(probe, """
      import java.util.Locale;
      public class Probe{ public static void main(String[] a){
        for (var k: a){ System.out.print("|"+(k.equals("locale") ? Locale.getDefault()+","+Locale.getDefault(Locale.Category.FORMAT)+","+Locale.getDefault(Locale.Category.DISPLAY) : System.getProperty(k))); }
      } }
      """);
    Fs.runTool("javac", List.of("-d", classes.toString(), src.toString(), probe.toString()));
  }
  static String probe(String... keys) throws InterruptedException{
    var out= new StringBuilder();
    var jvm= ChildJvm.start(Stream.concat(Stream.of("-cp", classes.toString(), "Probe"), Stream.of(keys)).toList(), out::append);
    assertEquals(0, jvm.await());
    return out.toString();
  }
  @Test void aChildKnowsNoLocaleAndNoEncodingButUtf8() throws InterruptedException{
    Err.strCmp("|,,|UTF-8|UTF-8|UTF-8|UTF-8", probe("locale", "file.encoding", "stdin.encoding", "stdout.encoding", "stderr.encoding"));
  }
  @Test void aChildNamesFilesInUtf8() throws InterruptedException{
    assumeFalse(Fs.isWindows());
    Err.strCmp("|UTF-8", probe("sun.jnu.encoding"));
  }
  @Test void killingAChildThatPrintsEndsAwaitNormally() throws InterruptedException{
    for (var i= 0; i < 20; i += 1){
      var printed= new boolean[1];
      var jvm= ChildJvm.start(List.of("-cp", classes.toString(), "Spam"), _ -> printed[0] = true);
      var end= System.nanoTime()+10_000_000_000L;
      while (!printed[0]){ assertTrue(System.nanoTime() < end); Thread.sleep(5); }
      jvm.kill();
      jvm.await();
      assertFalse(jvm.p().isAlive());
    }
  }
}
