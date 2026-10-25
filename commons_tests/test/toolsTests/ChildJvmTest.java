package toolsTests;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.ChildJvm;
import tools.Fs;

final class ChildJvmTest{
  @TempDir static Path classes;
  @BeforeAll static void compileSpam(){
    var src= classes.resolve("Spam.java");
    Fs.writeUtf8(src, "public class Spam{ public static void main(String[] a){ while (true){ System.out.println(\"spam\"); } } }\n");
    Fs.runTool("javac", List.of("-d", classes.toString(), src.toString()));
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
