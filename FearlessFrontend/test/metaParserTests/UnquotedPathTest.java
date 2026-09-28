package metaParserTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import fileAssociations.LinuxAssociations;
import tools.Fs;
import tools.JavacTool;
import utils.OneOr;

public class UnquotedPathTest{
  @Test void desktopExecQuotesCommandWithSpace(){
    var entry= LinuxAssociations.desktopEntry("fearless", "/opt/my apps/fearless/bin/fearless", "controller-Main", List.of("application/x-fear"));
    var exec= OneOr.of("one Exec line", entry.lines().filter(l->l.startsWith("Exec=")));
    assertEquals("Exec=\"/opt/my apps/fearless/bin/fearless\" %f", exec);
  }
  @Test void javacArgFileKeepsApostropheInSourcePath(@TempDir Path tmp){
    var src= tmp.resolve("it's").resolve("src");
    Fs.writeUtf8(src.resolve("A.java"), "class A{}\n");
    var classes= tmp.resolve("classes");
    Fs.ensureDir(classes);
    var jar= tmp.resolve("out").resolve("A.jar");
    Fs.ensureDir(jar.getParent());
    JavacTool.compileTree(src, classes, ()->{}, jar, List.of());
    assertTrue(Files.isRegularFile(classes.resolve("A.class")));
  }
}
