package toolsTests;

import static org.junit.jupiter.api.Assertions.assertFalse;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermissions;
import java.util.stream.Stream;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.Fs;

final class FsReadOnlyTest{
  @Test void rmTreeDeletesTheFilesAndFoldersThatTheOwnerCanNotChange(@TempDir Path tmp){
    var tree= tmp.resolve("tree");
    Fs.writeUtf8(tree.resolve("a/b/c.txt"), "c");
    Fs.writeUtf8(tree.resolve("a/d.txt"), "d");
    Stream.of("a/b/c.txt", "a/d.txt").forEach(n -> denied(tree.resolve(n), "r--r--r--"));
    denied(tree.resolve("a/b"), "---------");
    denied(tree.resolve("a"), "r-xr-xr-x");
    Fs.rmTree(tree);
    assertFalse(Files.exists(tree));
  }
  private static void denied(Path p, String permissions){
    if (Fs.isWindows()){ Fs.ofV(() -> Files.setAttribute(p, "dos:readonly", true)); return; }
    Fs.ofV(() -> Files.setPosixFilePermissions(p, PosixFilePermissions.fromString(permissions)));
  }
}
