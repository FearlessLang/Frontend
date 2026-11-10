package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

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
import java.util.function.ToIntFunction;

import javax.imageio.ImageIO;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import fileAssociations.FileAssociations;
import fileAssociations.Icon;
import fileAssociations.LinuxAssociations;
import fileAssociations.MacAssociations;
import fileAssociations.MacAssociations.Declared;
import tools.Fs;
import utils.Push;

/// FileAssociations on the desktop of the current desk:
/// on Linux a desktop made of the folders of a test, on Windows keys of the registry of the current user that only this test uses,
/// on macOS a folder of a test for the helper bundles and the types this test declares.
final class ReconcileTest{
  private static final String old= "fearlessCommonsTestProbe";
  private static final String identity= old+"New";
  private static final String ext= ".fcommonsprobe";
  private static final String fearlessExt= ".ffile999";
  private static final Predicate<String> family= s -> s.startsWith(old);
  private static final String hkcu= "HKEY_CURRENT_USER\\Software\\";
  private static final String fileExts= hkcu+"Microsoft\\Windows\\CurrentVersion\\Explorer\\FileExts\\";
  @TempDir Path tmp;
  private final List<Path> replaced= new ArrayList<>();
  private Function<String,String> env;
  private BiConsumer<List<String>,Function<String,RuntimeException>> run;
  private final Path home= MacAssociations.home;
  private final Function<String,List<Declared>> declared= MacAssociations.declared;
  private final ToIntFunction<Path> register= MacAssociations.register;
  private final BiConsumer<Path,String> offer= MacAssociations.offer;
  private final List<String> claims= new ArrayList<>();
  @BeforeEach void desktop(){
    if (Fs.isWindows()){ cleanUp(); return; }
    if (Fs.isMac()){
      MacAssociations.home = tmp.resolve("home");
      MacAssociations.declared = e -> claims.contains("."+e) ? List.of(new Declared("other."+e, Path.of("/Applications/other.app"))) : List.of();
      MacAssociations.register = _ -> 0;
      MacAssociations.offer = (_,_) -> {};
      return;
    }
    env = LinuxAssociations.env;
    run = LinuxAssociations.run;
    var vars= Map.of("XDG_DATA_HOME", tmp.resolve("home").toString(), "XDG_DATA_DIRS", tmp.resolve("sys").toString(),
      "XDG_CONFIG_HOME", tmp.resolve("config").toString(), "XDG_CONFIG_DIRS", tmp.resolve("etc").toString(), "XDG_CURRENT_DESKTOP", "");
    LinuxAssociations.env = vars::get;
    LinuxAssociations.run = (_,_) -> {};
  }
  @AfterEach void restore(){
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    if (Fs.isWindows()){ cleanUp(); return; }
    if (Fs.isMac()){
      MacAssociations.home = home;
      MacAssociations.declared = declared;
      MacAssociations.register = register;
      MacAssociations.offer = offer;
      return;
    }
    LinuxAssociations.env = env;
    LinuxAssociations.run = run;
  }
  private static void cleanUp(){
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    for (var e : List.of(ext, fearlessExt)){
      reg("delete", "HKCU\\Software\\Classes\\"+e, "/f");
      reg("delete", "HKCU\\Software\\Classes\\"+other(e), "/f");
      reg("delete", "HKCU\\Software\\Microsoft\\Windows\\CurrentVersion\\Explorer\\FileExts\\"+e, "/f");
    }
  }
  private static int reg(String... args){
    var p= Fs.of(new ProcessBuilder(Push.of("reg", List.of(args))).redirectErrorStream(true).redirectOutput(Redirect.DISCARD)::start);
    try{ return p.waitFor(); }
    catch (InterruptedException e){ throw new AssertionError(e); }
  }
  private void importReg(String keys){
    var file= tmp.resolve("probe.reg");
    Fs.ofV(() -> Files.write(file, ("﻿Windows Registry Editor Version 5.00\r\n"+keys).getBytes(StandardCharsets.UTF_16LE)));
    assertEquals(0, reg("import", file.toString()));
  }
  private static String regKey(String key, String name, String data){
    var shown= name.isEmpty() ? "@" : "\""+name+"\"";
    return "\r\n["+key+"]\r\n"+shown+"=\""+data.replace("\\", "\\\\").replace("\"", "\\\"")+"\"\r\n";
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
  private String refused(List<String> extensions){
    return assertThrows(IllegalStateException.class, () -> reconcile(identity, tmp.resolve("new").resolve("fearless"), extensions)).getMessage();
  }
  private static String other(String ext){ return Fs.isWindows() ? "otherProgram"+ext : "other"; }
  private void claim(String ext){
    if (Fs.isMac()){ claims.add(ext); return; }
    if (Fs.isLinux()){ Fs.writeUtf8(tmp.resolve("sys").resolve("applications").resolve("other.desktop"), "[Desktop Entry]\nMimeType="+LinuxAssociations.typeOf(ext)+";\n"); return; }
    importReg(regKey(hkcu+"Classes\\"+ext+"\\OpenWithProgids", other(ext), ""));
  }
  private boolean claimed(String ext){
    if (Fs.isMac()){ return claims.contains(ext); }
    if (Fs.isLinux()){ return Fs.readUtf8(tmp.resolve("sys").resolve("applications").resolve("other.desktop")).contains(LinuxAssociations.typeOf(ext)); }
    return reg("query", "HKCU\\Software\\Classes\\"+ext+"\\OpenWithProgids", "/v", other(ext)) == 0;
  }
  private void choose(String ext){
    if (Fs.isLinux()){ Fs.writeUtf8(tmp.resolve("config").resolve("mimeapps.list"), "[Default Applications]\n"+LinuxAssociations.typeOf(ext)+"=other.desktop\n"); return; }
    importReg(regKey(fileExts+ext+"\\UserChoice", "ProgId", other(ext)));
  }
  private void partial(String identity){
    if (Fs.isMac()){ Fs.ensureDir(MacAssociations.home.resolve(identity+".app")); return; }
    if (Fs.isLinux()){ Fs.writeUtf8(tmp.resolve("sys").resolve("applications").resolve(identity+".desktop"), "[Desktop Entry]\n"); return; }
    importReg(regKey(hkcu+identity+"\\Capabilities", "ApplicationName", identity));
  }
  private static List<String> handWritten(Path command){
    if (Fs.isWindows()){ return List.of(command+" \"%1\""); }
    if (Fs.isMac()){ return List.of("#!/bin/sh\n"+command+" \"$@\"\n"); }
    return List.of(command+" %F", command+" %f");
  }
  private void register(String command){
    if (Fs.isMac()){ Fs.writeUtf8(MacAssociations.home.resolve(old+".app").resolve("Contents").resolve("MacOS").resolve(old), command); return; }
    if (Fs.isLinux()){ Fs.writeUtf8(tmp.resolve("home").resolve("applications").resolve(old+".desktop"), "[Desktop Entry]\nExec="+command+"\n"); return; }
    importReg(regKey(hkcu+old+"\\Capabilities\\FileAssociations", ext, old+ext)+regKey(hkcu+"Classes\\"+old+ext+"\\shell\\open\\command", "", command));
  }
  @Test void takingOverAnotherProgramGivesItsCommandOnceAndKeepsItsSpacesAndBackslashes(){
    var oldCommand= tmp.resolve("my apps\\x").resolve("fearless");
    reconcile(old, oldCommand, List.of(ext));
    assertEquals(List.of(), replaced);
    reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of(ext));
    assertEquals(List.of(oldCommand), replaced);
    assertEquals(List.of(identity), FileAssociations.identities(family));
    reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of(ext, fearlessExt));
    assertEquals(List.of(oldCommand), replaced);
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
  @Test void aReconcileWithNoExtensionsRemovesTheIdentity(){
    reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of(ext, fearlessExt));
    assertEquals(List.of(identity), FileAssociations.identities(family));
    reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of());
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void aPartialRegistrationIsAnIdentityAndRemovingEveryIdentityRemovesIt(){
    partial(old);
    assertEquals(List.of(old), FileAssociations.identities(family));
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void aDefaultTheUserChoseForAnotherProgramLocksTheExtension(){
    assumeFalse(Fs.isMac());
    choose(ext);
    assertEquals("userLocked {"+ext+"=["+other(ext)+"]}", refused(List.of(ext)));
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void aFearlessExtensionAnotherProgramClaimsIsNotOurs(){
    claim(fearlessExt);
    assertEquals("notOurs {"+fearlessExt+"=["+other(fearlessExt)+"]}", refused(List.of(ext, fearlessExt)));
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void removingAnIdentityKeepsTheClaimOfAnotherProgramOnTheSameExtension(){
    claim(ext);
    reconcile(identity, tmp.resolve("new").resolve("fearless"), List.of(ext));
    assertEquals(List.of(identity), FileAssociations.identities(family));
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of(), FileAssociations.identities(family));
    assertTrue(claimed(ext));
  }
}
