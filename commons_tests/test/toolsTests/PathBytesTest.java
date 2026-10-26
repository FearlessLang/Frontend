package toolsTests;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.io.File;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.Fs;
import tools.PathBytes;
import tools.PathClassLoader;
import utils.Err;

final class PathBytesTest{
  @Test void aPathReadsBackFromItsBytes(@TempDir Path tmp){
    assumeTrue(Fs.isLinux());
    var odd= tmp.resolve(PathBytes.path(new byte[]{'c', 'a', 'f', (byte)0xE9}));
    Fs.ensureDir(odd);
    var bytes= PathBytes.of(odd);
    assertEquals((byte)0xE9, bytes[bytes.length-1]);
    assertEquals(odd, PathBytes.path(bytes));
    assertEquals(Path.of("a", "b"), PathBytes.path("a/b".getBytes()));
    assertEquals(Path.of(""), PathBytes.path(new byte[0]));
    assertArrayEquals("/".getBytes(), PathBytes.of(Path.of("/")));
  }
  @Test void anArgumentIsReadAsTheBytesTheProcessReceived(@TempDir Path tmp) throws Exception{
    assumeTrue(Fs.isLinux());
    var src= tmp.resolve("ArgProbe.java");
    Fs.writeUtf8(src, "public class ArgProbe{ public static void main(String[] a){ System.out.print(tools.PathClassLoader.argOf(tools.PathBytes.arg(a, 1).toAbsolutePath())); } }\n");
    Fs.runTool("javac", List.of("-d", tmp.toString(), "-cp", PathClassLoader.jar().toString(), src.toString()));
    var java= Path.of(System.getProperty("java.home"), "bin", "java").toString();
    var pb= new ProcessBuilder("sh", "-c", "exec \"$0\" -ea -cp \"$1\" ArgProbe x \"$(printf '/tmp/caf\\351')\"", java, tmp+File.pathSeparator+PathClassLoader.jar());
    pb.environment().put("LC_ALL", "C.UTF-8");
    var p= pb.redirectErrorStream(true).start();
    var out= new String(p.getInputStream().readAllBytes());
    assertEquals(0, p.waitFor(), out);
    Err.strCmp("file:///tmp/caf%E9", out);
  }
}
