package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
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
  private static Map<String,byte[]> read(byte[] zip){
    return new ReadZip(
      n -> new IllegalStateException("badName "+n),
      n -> new IllegalStateException("dupName "+n),
      n -> new IllegalStateException("tooLarge "+n),
      n -> new IllegalStateException("emptyDir "+n),
      (_,_) -> {}
    ).readAll(() -> new ZipInputStream(new ByteArrayInputStream(zip)));
  }
  @Test void aFolderEntryAndAFileOfTheSameNameAreRefused(){
    assertEquals("dupName a", assertThrows(IllegalStateException.class, () -> read(zip("a/", "a/b", "a"))).getMessage());
  }
  @Test void aFileAndAFileInsideAFolderOfTheSameNameAreAccepted(){
    assertEquals(List.of("a", "a/b"), List.copyOf(read(zip("a", "a/b")).keySet()));
    assertEquals(List.of("a/b", "a"), List.copyOf(read(zip("a/b", "a")).keySet()));
  }
}
