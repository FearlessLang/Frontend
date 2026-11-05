package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.awt.image.BufferedImage;
import java.lang.ProcessBuilder.Redirect;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;

import javax.imageio.ImageIO;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import fileAssociations.FileAssociations;
import fileAssociations.Icon;
import fileAssociations.LinuxAssociations;
import tools.Fs;
import utils.Push;

/// The command that reconcile gives to replaced, on the desktop of the current desk:
/// on Linux a desktop made of the folders of a test, on Windows keys of the registry of the current user that only this test uses.
final class ReplacedCommandTest{
  private static final String old= "fearlessCommonsTestProbe";
  private static final String identity= old+"New";
  private static final String ext= ".fcommonsprobe";
  private static final Predicate<String> family= s -> s.startsWith(old);
  @TempDir Path tmp;
  private final List<Path> replaced= new ArrayList<>();
  private Function<String,String> env;
  private BiConsumer<List<String>,Function<String,RuntimeException>> run;
  @BeforeEach void desktop(){
    assumeTrue(Fs.isLinux() || Fs.isWindows());
    if (Fs.isWindows()){ FileAssociations.eradicateAll(family, IllegalStateException::new); return; }
    env = LinuxAssociations.env;
    run = LinuxAssociations.run;
    var vars= Map.of("XDG_DATA_HOME", tmp.resolve("home").toString(), "XDG_DATA_DIRS", tmp.resolve("sys").toString(),
      "XDG_CONFIG_HOME", tmp.resolve("config").toString(), "XDG_CONFIG_DIRS", tmp.resolve("etc").toString(), "XDG_CURRENT_DESKTOP", "");
    LinuxAssociations.env = vars::get;
    LinuxAssociations.run = (_,_) -> {};
  }
  @AfterEach void restore(){
    if (!Fs.isLinux() && !Fs.isWindows()){ return; }
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    if (env == null){ return; }
    LinuxAssociations.env = env;
    LinuxAssociations.run = run;
  }
  private Path png(){
    var file= tmp.resolve("icon.png");
    Fs.ofV(() -> ImageIO.write(new BufferedImage(64, 64, BufferedImage.TYPE_INT_RGB), "png", file.toFile()));
    return file;
  }
  private void reconcile(String identity, Path command, List<String> extensions){
    var icons= extensions.stream().map(e -> new Icon(e, tmp.resolve("icon.ico"), png())).toList();
    FileAssociations.reconcile(identity, family, command, icons, List.of(), tmp.resolve("icon.ico"), png(), replaced::add,
      s -> new IllegalStateException("ambiguous "+s),
      s -> new IllegalStateException("userLocked "+s),
      s -> new IllegalStateException("notOurs "+s),
      s -> new IllegalStateException("notWritable "+s),
      s -> new IllegalStateException("halfDone "+s));
  }
  private List<Path> replacedFrom(Path oldCommand){
    reconcile(old, oldCommand, List.of(ext));
    assertEquals(List.of(), replaced);
    reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of());
    assertEquals(List.of(), FileAssociations.identities(family));
    return replaced;
  }
  @Test void theCommandOfAnotherProgramKeepsItsSpacesAndBackslashes(){
    var oldCommand= tmp.resolve("my apps\\x").resolve("fearless");
    assertEquals(List.of(oldCommand), replacedFrom(oldCommand));
  }
  private static List<String> handWritten(Path command){
    if (Fs.isWindows()){ return List.of(command+" \"%1\""); }
    return List.of(command+" %F", command+" %f");
  }
  private void register(String command){
    if (Fs.isLinux()){ Fs.writeUtf8(tmp.resolve("home").resolve("applications").resolve(old+".desktop"), "[Desktop Entry]\nExec="+command+"\n"); return; }
    var progId= old+ext;
    var value= command.replace("\\", "\\\\").replace("\"", "\\\"");
    var content= "Windows Registry Editor Version 5.00\r\n\r\n"
      +"[HKEY_CURRENT_USER\\Software\\"+old+"\\Capabilities\\FileAssociations]\r\n\""+ext+"\"=\""+progId+"\"\r\n\r\n"
      +"[HKEY_CURRENT_USER\\Software\\Classes\\"+progId+"\\shell\\open\\command]\r\n@=\""+value+"\"\r\n";
    var file= tmp.resolve("probe.reg");
    Fs.ofV(() -> Files.write(file, ("﻿"+content).getBytes(StandardCharsets.UTF_16LE)));
    var p= Fs.of(new ProcessBuilder(Push.of("reg", List.of("import", file.toString()))).redirectErrorStream(true).redirectOutput(Redirect.DISCARD)::start);
    try{ assertEquals(0, p.waitFor()); }
    catch (InterruptedException e){ throw new AssertionError(e); }
  }
  @Test void aFamilyRegistrationNotWrittenByReconcileNamesNoCommand(){
    for (var command : handWritten(tmp.resolve("old").resolve("fearless"))){
      register(command);
      assertEquals(List.of(old), FileAssociations.identities(family));
      reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of());
      assertEquals(List.of(), replaced);
      assertEquals(List.of(), FileAssociations.identities(family));
    }
  }
}
