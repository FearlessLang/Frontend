package toolsTests;

import static org.junit.jupiter.api.Assumptions.assumeFalse;

import java.net.URI;
import java.nio.file.Path;

import tools.Fs;

final class NotUnicode{
  static Path in(Path dir){
    assumeFalse(Fs.isMac());
    if (Fs.isWindows()){ return dir.resolve("caf\ud800"); }
    return Path.of(URI.create(dir.toUri()+"caf%E9"));
  }
}
