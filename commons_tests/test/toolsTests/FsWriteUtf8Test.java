package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import tools.Fs;

final class FsWriteUtf8Test{
  @Test void aFileNameWithoutFolderIsWritten(){
    var file= Path.of("fs_write_utf8_test.txt");
    try{
      Fs.writeUtf8(file, "a");
      assertEquals("a", Fs.readUtf8(file));
    }
    finally{ Fs.ofV(() -> Fs.deleteIfExists(file)); }
  }
}
