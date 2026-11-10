package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

import org.junit.jupiter.api.Test;

import tools.Fs;
import tools.ReadZip;

final class ReadZipTest{
  private static byte[] zip(String... names){
    var res= new ByteArrayOutputStream();
    Fs.ofV(() -> write(res, names));
    return res.toByteArray();
  }
  private static void write(ByteArrayOutputStream out, String... names) throws IOException{
    try (var z= new ZipOutputStream(out)){
      for (var n : names){
        z.putNextEntry(new ZipEntry(n));
        if (!n.endsWith("/")){ z.write(1); }
        z.closeEntry();
      }
    }
  }
  private static final ReadZip reader= new ReadZip(
    n -> new IllegalStateException("badName "+n),
    n -> new IllegalStateException("dupName "+n),
    n -> new IllegalStateException("tooLarge "+n),
    n -> new IllegalStateException("emptyDir "+n),
    (_,_) -> {});
  private static Map<String,byte[]> read(byte[] zip){ return reader.readAll(() -> new ZipInputStream(new ByteArrayInputStream(zip))); }
  private static Map<String,byte[]> read(byte[] zip, String kept){ return reader.read(() -> new ZipInputStream(new ByteArrayInputStream(zip)), kept::equals); }
  private static String refused(String... names){
    return assertThrows(IllegalStateException.class, () -> read(zip(names))).getMessage();
  }
  @Test void aFolderEntryWithNothingInsideIsRefused(){
    assertEquals("emptyDir a", refused("a/", "b"));
    assertEquals("emptyDir .a", refused(".a/", "b"));
    assertEquals("emptyDir a/.b", refused("a/.b/", "a/c"));
    assertEquals("emptyDir a.b/c", refused("a.b/c/"));
  }
  @Test void aFolderEntryWithNothingInsideIsKeptInsideAFolderWhoseNameStartsWithADot(){
    assertEquals(List.of(".a/c/", "b"), List.copyOf(read(zip(".a/", ".a/c/", "b")).keySet()));
    assertEquals(List.of("a/.b/c/e/", "a/.b/d"), List.copyOf(read(zip("a/.b/c/", "a/.b/c/e/", "a/.b/d")).keySet()));
    assertEquals(0, read(zip(".a/c/")).get(".a/c/").length);
  }
  @Test void aFolderEntryAndAFileOfTheSameNameAreRefused(){
    assertEquals("dupName a", assertThrows(IllegalStateException.class, () -> read(zip("a/", "a/b", "a"))).getMessage());
  }
  @Test void aReadKeepsTheBytesOfTheKeptFileOnlyAndNamesEveryFile(){
    var res= read(zip("a/", "a/b", "c", "d/e"), "c");
    assertEquals(List.of("a/b", "c", "d/e"), List.copyOf(res.keySet()));
    assertEquals(Arrays.asList(null, "[1]", null), res.values().stream().map(v -> v == null ? null : Arrays.toString(v)).toList());
    assertEquals(List.of(".a/c/", "b"), List.copyOf(read(zip(".a/", ".a/c/", "b"), "b").keySet()));
  }
  @Test void aReadChecksTheFilesItDoesNotKeep(){
    assertEquals("dupName b", assertThrows(IllegalStateException.class, () -> read(zip("a", "b/", "b/c", "b"), "a")).getMessage());
    assertEquals("emptyDir d", assertThrows(IllegalStateException.class, () -> read(zip("c", "d/"), "c")).getMessage());
  }
}
