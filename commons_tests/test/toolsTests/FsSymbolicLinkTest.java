package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.FileSystemException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;
import org.junit.jupiter.api.io.TempDir;

import tools.Fs;
import utils.Err;

final class FsSymbolicLinkTest{
  @TempDir Path root;
  private static Path link(Path link, Path target){
    try{ return Files.createSymbolicLink(link, target); }
    catch (FileSystemException e){
      if (!Fs.isWindows()){ throw new UncheckedIOException(e); }
      return Assumptions.abort("Windows does not give this process the privilege to create symbolic links");
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
  }
  private static void refused(Executable e){
    var msg= assertThrows(IllegalArgumentException.class, e).getMessage();
    Err.strCmp("\"[###]\" is a symbolic link; Fs does not read, write, copy or delete through symbolic links: replace it with the file or folder it points to.", msg);
  }
  @Test void everyOperationRefusesALink(){
    var file= root.resolve("f.txt");
    Fs.writeUtf8(file, "x");
    var real= root.resolve("real");
    Fs.writeUtf8(real.resolve("f.txt"), "x");
    var fileLink= link(root.resolve("l.txt"), file);
    var dirLink= link(root.resolve("ldir"), real);
    List.<Executable>of(
      () -> Fs.readUtf8(fileLink),
      () -> Fs.writeUtf8(fileLink, "y"),
      () -> Fs.lastModified(fileLink),
      () -> Fs.ensureDir(dirLink),
      () -> Fs.reqDir(dirLink, "a test"),
      () -> Fs.cleanDir(dirLink),
      () -> Fs.rmTree(dirLink),
      () -> Fs.copyTree(dirLink, root.resolve("to")),
      () -> Fs.copyTreeFlat(dirLink, root.resolve("to")),
      () -> Fs.copyTree(real, dirLink),
      () -> Fs.walk(dirLink, s -> s.toList()),
      () -> Fs.realPath(dirLink)
    ).forEach(FsSymbolicLinkTest::refused);
    assertEquals("x", Fs.readUtf8(file));
    assertEquals("x", Fs.readUtf8(real.resolve("f.txt")));
    assertFalse(Files.exists(root.resolve("to")));
  }
  @Test void aLinkInsideATreeStopsTheOperationBeforeAnyChange(){
    var real= root.resolve("real");
    Fs.writeUtf8(real.resolve("f.txt"), "x");
    var dir= root.resolve("dir");
    Fs.writeUtf8(dir.resolve("a.txt"), "a");
    link(dir.resolve("link"), real);
    refused(() -> Fs.cleanDir(dir));
    refused(() -> Fs.rmTree(dir));
    refused(() -> Fs.copyTree(dir, root.resolve("to")));
    assertEquals("a", Fs.readUtf8(dir.resolve("a.txt")));
    assertEquals("x", Fs.readUtf8(real.resolve("f.txt")));
    assertFalse(Files.exists(root.resolve("to")));
  }
  @Test void theConfiguredErrorIsThrown(){
    var file= root.resolve("f.txt");
    Fs.writeUtf8(file, "x");
    var fileLink= link(root.resolve("l.txt"), file);
    var old= Fs.onSymbolicLink;
    Fs.onSymbolicLink= p -> new IllegalStateException("configured for "+p.getFileName());
    try{ assertEquals("configured for l.txt", assertThrows(IllegalStateException.class, () -> Fs.readUtf8(fileLink)).getMessage()); }
    finally{ Fs.onSymbolicLink= old; }
  }
}
