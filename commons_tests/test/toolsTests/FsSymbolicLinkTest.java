package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.FileTime;
import java.time.Duration;
import java.util.List;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import tools.Fs;

final class FsSymbolicLinkTest{
  @TempDir Path root;
  @BeforeEach void links(){ assumeFalse(Fs.isWindows()); }
  private Path real(){
    var res= root.resolve("real");
    Fs.writeUtf8(res.resolve("f.txt"), "x");
    return res;
  }
  private static Path link(Path link, Path target){ return Fs.of(() -> Files.createSymbolicLink(link, target)); }
  private static List<String> names(Path dir){
    return Fs.of(() -> { try (var s= Files.list(dir)){ return s.map(p -> p.getFileName().toString()).sorted().toList(); }});
  }
  @Test void cleanDirThroughALinkEmptiesTheLinkedFolder(){
    var real= real();
    Fs.cleanDir(link(root.resolve("link"), real));
    assertEquals(List.of(), names(real));
  }
  @Test void cleanDirDeletesALinkInsideButNotTheLinkedFolder(){
    var real= real();
    var dir= root.resolve("dir");
    Fs.ensureDir(dir);
    link(dir.resolve("link"), real);
    Fs.cleanDir(dir);
    assertEquals(List.of(), names(dir));
    assertEquals(List.of("f.txt"), names(real));
  }
  @Test void rmTreeOfALinkDeletesOnlyTheLink(){
    var real= real();
    var link= link(root.resolve("link"), real);
    Fs.rmTree(link);
    assertEquals(List.of("real"), names(root));
    assertEquals(List.of("f.txt"), names(real));
  }
  @Test void copyTreeCopiesTheContentOfALinkedFolder(){
    var from= root.resolve("from");
    Fs.writeUtf8(from.resolve("top.txt"), "t");
    link(from.resolve("sub"), real());
    var to= root.resolve("to");
    Fs.copyTree(from, to);
    assertEquals(List.of("f.txt"), names(to.resolve("sub")));
  }
  @Test void copyTreeFlatCopiesTheFilesOfALinkedFolder(){
    var from= root.resolve("from");
    Fs.writeUtf8(from.resolve("top.txt"), "t");
    link(from.resolve("sub"), real());
    var to= root.resolve("to");
    Fs.copyTreeFlat(from, to);
    assertEquals(List.of("f.txt", "top.txt"), names(to));
  }
  @Test void lastModifiedOfALinkIsTheTimeOfTheLinkedFile(){
    var file= root.resolve("f.txt");
    Fs.writeUtf8(file, "x");
    var link= link(root.resolve("l.txt"), file);
    Fs.ofV(() -> Files.setLastModifiedTime(file, FileTime.fromMillis(1_000_000_000_000L)));
    assertEquals(1_000_000_000_000L, Fs.lastModified(link));
  }
  @Test void writeUtf8WithAMinimumTimeThroughALinkReturns(){
    var file= root.resolve("f.txt");
    Fs.writeUtf8(file, "x");
    var link= link(root.resolve("l.txt"), file);
    var min= Fs.lastModified(link);
    assertTimeoutPreemptively(Duration.ofSeconds(5), () -> Fs.writeUtf8(link, "y", min));
    assertEquals("y", Fs.readUtf8(file));
  }
}
