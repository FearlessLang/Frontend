package toolsTests;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.Fs;
import tools.PathBytes;
import tools.PathClassLoader;
import utils.Push;

final class PathBytesTest{
  private static Path odd(Path tmp){
    var dir= tmp.resolve("caf\u00e9 \ud83d\ude00 \u4e2d");
    var res= Fs.isMac() ? dir : NotUnicode.in(dir);
    Fs.ensureDir(res);
    return res;
  }
  @Test void aFolderNameThatIsNotUnicodeIsHeldOnLinuxAndWindowsAndRefusedOnMacOS(@TempDir Path tmp){
    if (Fs.isMac()){ assertThrows(IOException.class, () -> Files.createDirectory(Path.of(URI.create(tmp.toUri()+"caf%E9")))); return; }
    var odd= NotUnicode.in(tmp);
    Fs.ensureDir(odd);
    assertEquals(List.of(odd), Fs.of(() -> { try (var s= Files.list(tmp)){ return s.toList(); } }));
  }
  @Test void aPathReadsBackFromTheUnitsOfThisSystem(@TempDir Path tmp){
    var odd= odd(tmp);
    if (Fs.isWindows()){ assertEquals(odd, Path.of(new String(odd.toString().toCharArray()))); return; }
    assertEquals(odd, PathBytes.path(PathBytes.of(odd)));
    assertEquals(Path.of("a", "b"), PathBytes.path("a/b".getBytes()));
    assertEquals(Path.of(""), PathBytes.path(new byte[0]));
    assertArrayEquals("/".getBytes(), PathBytes.of(Path.of("/")));
  }
  private static List<String> withArg(List<String> cmd, Path arg){
    if (!Fs.isLinux()){ return Push.<String>of(cmd, List.of(arg.toString())); }
    var bytes= PathBytes.of(arg);
    var octal= IntStream.range(0, bytes.length).mapToObj(i -> "\\%03o".formatted(bytes[i] & 0xFF)).collect(Collectors.joining());
    return Push.<String>of(List.of("sh", "-c", "exec \"$@\" \"$(printf '"+octal+"')\"", "sh"), cmd);
  }
  @Test void anArgumentAndAPropertyNamingAFolderReachTheChildAsThatFolder(@TempDir Path tmp) throws Exception{
    var odd= odd(tmp);
    var src= tmp.resolve("ArgProbe.java");
    Fs.writeUtf8(src, "public class ArgProbe{ public static void main(String[] a){ System.out.print(tools.PathClassLoader.argOf(tools.PathBytes.arg(a, 1))+\"\\n\"+tools.PathClassLoader.argOf(tools.PathClassLoader.pathOf(System.getProperty(\"odd\")))); } }\n");
    Fs.runTool("javac", List.of("-d", tmp.toString(), "-cp", PathClassLoader.jar().toString(), src.toString()));
    var java= Path.of(System.getProperty("java.home"), "bin", "java").toString();
    var cmd= List.of(java, "-ea", "--enable-native-access=ALL-UNNAMED", "-Dodd="+PathClassLoader.argOf(odd), "-cp", tmp+File.pathSeparator+PathClassLoader.jar(), "ArgProbe", "x");
    var pb= new ProcessBuilder(withArg(cmd, odd));
    pb.environment().put("LC_ALL", "C.UTF-8");
    var p= pb.redirectErrorStream(true).start();
    var out= new String(p.getInputStream().readAllBytes());
    assertEquals(0, p.waitFor(), out);
    assertEquals(PathClassLoader.argOf(odd)+"\n"+PathClassLoader.argOf(odd), out);
  }
}
