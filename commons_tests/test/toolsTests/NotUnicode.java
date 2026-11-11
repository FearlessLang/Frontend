package toolsTests;

import java.net.URI;
import java.nio.file.Path;

import tools.Fs;

final class NotUnicode{
  static Path in(Path dir){
    if (Fs.isMac()){ return dir.resolve("caf\u00e9 \ud83d\ude00 \u4e2d"); }
    if (Fs.isWindows()){ return dir.resolve("caf\ud800"); }
    return Path.of(URI.create(dir.toUri()+"caf%E9"));
  }
}
