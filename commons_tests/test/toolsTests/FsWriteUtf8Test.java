package toolsTests;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import tools.Fs;

final class FsWriteUtf8Test{
  @Test void aFileNameWithoutFolderThrowsNullPointerException(){
    var file= Path.of("fs_write_utf8_test.txt");
    try{ assertThrows(NullPointerException.class, () -> Fs.writeUtf8(file, "a")); }
    finally{ Fs.ofV(() -> Fs.deleteIfExists(file)); }
  }
}
