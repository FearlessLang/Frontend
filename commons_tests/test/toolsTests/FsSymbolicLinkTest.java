package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.FileSystemException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardWatchEventKinds;
import java.nio.file.attribute.FileTime;
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
      () -> Fs.exists(fileLink),
      () -> Fs.notExists(fileLink),
      () -> Fs.isDirectory(dirLink),
      () -> Fs.isRegularFile(fileLink),
      () -> Fs.readAllBytes(fileLink),
      () -> Fs.newInputStream(fileLink).close(),
      () -> Fs.write(fileLink, new byte[0]),
      () -> Fs.writeString(fileLink, "y"),
      () -> Fs.move(fileLink, root.resolve("moved.txt")),
      () -> Fs.move(file, fileLink),
      () -> Fs.delete(fileLink),
      () -> Fs.deleteIfExists(fileLink),
      () -> Fs.createDirectories(dirLink),
      () -> Fs.list(dirLink).close(),
      () -> Fs.list(root).toList(),
      () -> Fs.size(fileLink),
      () -> Fs.getLastModifiedTime(fileLink),
      () -> Fs.setLastModifiedTime(fileLink, FileTime.fromMillis(0)),
      () -> Fs.getFileStore(fileLink),
      () -> Fs.openChannel(fileLink).close(),
      () -> Fs.watch(dirLink, root.getFileSystem().newWatchService(), StandardWatchEventKinds.ENTRY_CREATE)
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
  @Test void aJlinkLegalNoticeLinkIsAccepted(){
    var image= root.resolve("image");
    Fs.writeUtf8(image.resolve("legal/java.base/LICENSE"), "x");
    Fs.ensureDir(image.resolve("legal/java.naming"));
    var notice= link(image.resolve("legal/java.naming/LICENSE"), Path.of("..", "java.base", "LICENSE"));
    assertEquals("x", Fs.readUtf8(notice));
    Fs.copyTree(image, root.resolve("to"));
    assertFalse(Files.isSymbolicLink(root.resolve("to/legal/java.naming/LICENSE")));
    assertEquals("x", Fs.readUtf8(root.resolve("to/legal/java.naming/LICENSE")));
    Fs.rmTree(image);
    assertFalse(Files.exists(image));
  }
  @Test void aLinkToAnotherLegalNoticeIsRefused(){
    var image= root.resolve("image");
    Fs.writeUtf8(image.resolve("legal/java.base/LICENSE"), "x");
    Fs.ensureDir(image.resolve("legal/java.naming"));
    link(image.resolve("legal/java.naming/COPYRIGHT"), Path.of("..", "java.base", "LICENSE"));
    refused(() -> Fs.rmTree(image));
    assertEquals("x", Fs.readUtf8(image.resolve("legal/java.base/LICENSE")));
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
