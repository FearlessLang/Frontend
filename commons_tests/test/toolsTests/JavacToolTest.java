package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.zip.ZipInputStream;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.Fs;
import tools.JavacTool;

final class JavacToolTest{
  private static void compiles(Path folder){
    var src= folder.resolve("src");
    Fs.writeUtf8(src.resolve("A.java"), "class A{}\n");
    var classes= folder.resolve("classes");
    Fs.ensureDir(classes);
    var jar= folder.resolve("out").resolve("A.jar");
    Fs.ensureDir(jar.getParent());
    Fs.of(() -> JavacTool.compileTree(src, classes, () -> {}, jar, List.of()));
    assertTrue(Files.isRegularFile(classes.resolve("A.class")));
    assertEquals(List.of("META-INF/MANIFEST.MF", "A.class"), Fs.of(() -> entries(jar)));
  }
  private static List<String> entries(Path jar) throws IOException{
    try (var in= new ZipInputStream(Files.newInputStream(jar))){
      var res= new ArrayList<String>();
      for (var e= in.getNextEntry(); e != null; e= in.getNextEntry()){ res.add(e.getName()); }
      return res;
    }
  }
  @Test void apostropheInProjectFolder(@TempDir Path tmp){ compiles(tmp.resolve("it's")); }
  @Test void backslashInProjectFolder(@TempDir Path tmp){ compiles(tmp.resolve("a\\b")); }
  @Test void projectFolderWhoseNameIsNotUtf8(@TempDir Path tmp){
    assumeTrue(Fs.isLinux());
    compiles(Path.of(URI.create(tmp.toUri()+"caf%E9")));
  }
  @Test void managerFolderIsNextToTheProgramFolderOfTheLauncher(){
    var dir= Path.of("opt", "fearlessManaged0_002");
    assertEquals(Optional.of(dir.resolveSibling("fearless0_002")), JavacTool.managerFolderOf(dir.resolve("fearlessManaged0_002w.exe")));
    assertEquals(Optional.of(dir.resolveSibling("fearless0_002")), JavacTool.managerFolderOf(dir.resolve("bin").resolve("fearlessManaged0_002")));
    assertEquals(Optional.empty(), JavacTool.managerFolderOf(Path.of("opt", "fearless0_002", "bin", "fearless0_002")));
  }
}
