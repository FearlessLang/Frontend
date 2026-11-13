package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.awt.image.BufferedImage;
import java.lang.ProcessBuilder.Redirect;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.ToIntFunction;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import javax.imageio.ImageIO;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.opentest4j.AssertionFailedError;

import fileAssociations.FileAssociations;
import fileAssociations.Icon;
import fileAssociations.LinuxAssociations;
import fileAssociations.MacAssociations;
import fileAssociations.MacAssociations.Declared;
import tools.Fs;
import utils.Err;
import utils.Push;

/// FileAssociations on the desktop of the current desk:
/// on Linux a desktop made of the folders of a test, on Windows keys of the registry of the current user that only this test uses,
/// on macOS a folder of a test for the helper bundles, a preferences domain that only this test uses, and the holders and the types this test gives.
final class ReconcileTest{
  static{ Err.setUp(AssertionFailedError.class, Assertions::assertEquals, Assertions::assertTrue); }
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
  private final Function<String,Optional<Path>> holder= MacAssociations.holder;
  private final String preferences= MacAssociations.preferences;
  private final List<String> reload= MacAssociations.reload;
  private final List<String> claims= new ArrayList<>();
  private final Map<String,Path> holders= new HashMap<>();
  private final Path lockFolder= FileAssociations.lockFolder;
  @BeforeEach void desktop(){
    FileAssociations.lockFolder = tmp.resolve("data");
    if (Fs.isWindows()){ cleanUp(); return; }
    if (Fs.isMac()){
      MacAssociations.home = tmp.resolve("home");
      MacAssociations.declared = e -> claims.contains("."+e) ? List.of(new Declared("other."+e, Path.of("/Applications/other.app"))) : List.of();
      MacAssociations.register = _ -> 0;
      MacAssociations.holder = this::holderOnTheDesk;
      MacAssociations.preferences = "fearless_test_"+tmp.getFileName();
      MacAssociations.reload = List.of("true");
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
    desktopRestored();
    FileAssociations.lockFolder = lockFolder;
  }
  private void desktopRestored(){
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    if (Fs.isWindows()){ cleanUp(); return; }
    if (Fs.isMac()){
      MacAssociations.home = home;
      MacAssociations.declared = declared;
      MacAssociations.register = register;
      MacAssociations.holder = holder;
      defaults("delete", MacAssociations.preferences);
      Fs.ofV(() -> Files.deleteIfExists(Path.of(System.getProperty("user.home"), "Library", "Preferences", MacAssociations.preferences+".plist")));
      MacAssociations.preferences = preferences;
      MacAssociations.reload = reload;
      return;
    }
    LinuxAssociations.env = env;
    LinuxAssociations.run = run;
  }
  private Optional<Path> holderOnTheDesk(String ext){
    var choice= Pattern.compile("\"LSHandlerContentType\":\""+Pattern.quote(MacAssociations.typeOf(identity, ext))+"\",\"LSHandlerRoleAll\":\"([^\"]*)\"").matcher(choicesOfTheDesk());
    return choice.find() ? Optional.of(Path.of("/Applications/"+choice.group(1)+".app")) : Optional.ofNullable(holders.get(ext));
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
  static int defaults(String... args){
    var p= Fs.of(new ProcessBuilder(Push.of("defaults", List.of(args))).redirectErrorStream(true).redirectOutput(Redirect.DISCARD)::start);
    try{ return p.waitFor(); }
    catch (InterruptedException e){ throw new AssertionError(e); }
  }
  static void pick(String type, String program){
    var entry= "<dict><key>LSHandlerContentType</key><string>"+type+"</string><key>LSHandlerRoleAll</key><string>"+program+"</string></dict>";
    assertEquals(0, defaults("write", MacAssociations.preferences, "LSHandlers", "-array-add", entry));
  }
  static String choicesOfTheDesk(){
    var p= Fs.of(new ProcessBuilder("/bin/sh", "-c", "defaults export \""+MacAssociations.preferences+"\" - | plutil -extract LSHandlers json -o - -").redirectErrorStream(true)::start);
    return new String(Fs.of(() -> p.getInputStream().readAllBytes()), StandardCharsets.UTF_8);
  }
  static String choices(String program, String... types){ return Stream.of(types).map(t -> "{\"LSHandlerContentType\":\""+t+"\",\"LSHandlerRoleAll\":\""+program+"\"}").collect(Collectors.joining(",", "[", "]")); }
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
  private Path command(){ return tmp.resolve("new").resolve("fearless"); }
  private void reconcile(String identity, Path command, List<String> extensions){ reconcile(identity, command, extensions, List.of()); }
  private void reconcile(String identity, Path command, List<String> extensions, List<String> taken){
    var icons= extensions.stream().map(e -> new Icon(e, tmp.resolve("icon.ico"), png())).toList();
    FileAssociations.reconcile(identity, identity, family, command, icons, taken, List.of(), png(), replaced::add,
      s -> new IllegalStateException("ambiguous "+s),
      s -> new IllegalStateException("notOurs "+s),
      s -> new IllegalStateException("notTaken "+s),
      s -> new IllegalStateException("notWritable "+s),
      s -> new IllegalStateException("halfDone "+s));
  }
  private String refused(List<String> extensions, List<String> taken){
    return assertThrows(IllegalStateException.class, () -> reconcile(identity, command(), extensions, taken)).getMessage();
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
  private void registered(String program, String... extensions){
    if (Fs.isMac()){ Stream.of(extensions).forEach(e -> holders.put(e, Path.of("/Applications/"+program+".app"))); return; }
    if (Fs.isWindows()){ Stream.of(extensions).forEach(e -> importReg(regKey(hkcu+"Classes\\"+e, "", program+e))); return; }
    var types= Stream.of(extensions).map(e -> "application/x-probe-"+e.substring(1)).toList();
    Fs.writeUtf8(tmp.resolve("sys").resolve("mime").resolve("globs2"), String.join("", Stream.of(extensions).map(e -> "50:application/x-probe-"+e.substring(1)+":*"+e+"\n").toList()));
    Fs.writeUtf8(tmp.resolve("sys").resolve("applications").resolve(program+".desktop"), "[Desktop Entry]\nMimeType="+String.join(";", types)+";\n");
  }
  private void preferred(String program, String ext){
    if (Fs.isMac()){ pick(MacAssociations.typeOf(identity, ext), program); return; }
    if (Fs.isWindows()){ importReg(regKey(fileExts+ext+"\\UserChoice", "ProgId", program+ext)); return; }
    Fs.writeUtf8(tmp.resolve("home").resolve("mime").resolve("globs2"), "100:"+LinuxAssociations.typeOf(ext)+":*"+ext+"\n");
    Fs.writeUtf8(tmp.resolve("sys").resolve("applications").resolve(program+".desktop"), "[Desktop Entry]\n");
    Fs.writeUtf8(tmp.resolve("config").resolve("mimeapps.list"), "[Default Applications]\ntext/plain="+program+".desktop\n"+LinuxAssociations.typeOf(ext)+"="+program+".desktop\n");
  }
  private String preferenceLeft(String ext){
    if (Fs.isMac()){ return choicesOfTheDesk(); }
    if (Fs.isWindows()){ return reg("query", fileExts+ext+"\\UserChoice") == 0 ? "UserChoice of "+ext : ""; }
    return Fs.readUtf8(tmp.resolve("config").resolve("mimeapps.list"));
  }
  private static String preference(String program){
    if (Fs.isMac()){ return choices(program, MacAssociations.typeOf(identity, ext)); }
    if (Fs.isWindows()){ return "UserChoice of "+ext; }
    return "[Default Applications]\ntext/plain="+program+".desktop\n"+LinuxAssociations.typeOf(ext)+"="+program+".desktop\n";
  }
  private static String noPreference(String program){
    if (Fs.isMac()){ return choices(identity, MacAssociations.typeOf(identity, ext)); }
    return Fs.isWindows() ? "" : "[Default Applications]\ntext/plain="+program+".desktop\n";
  }
  private static String regOut(String... args){
    var p= Fs.of(new ProcessBuilder(Push.of("reg", List.of(args))).redirectErrorStream(true)::start);
    return Fs.of(() -> new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8));
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
    reconcile(identity, command(), List.of(ext));
    assertEquals(List.of(oldCommand), replaced);
    assertEquals(List.of(identity), FileAssociations.identities(family));
    reconcile(identity, command(), List.of(ext, fearlessExt));
    assertEquals(List.of(oldCommand), replaced);
  }
  @Test void aFamilyRegistrationNotWrittenByReconcileNamesNoCommand(){
    for (var command : handWritten(tmp.resolve("old").resolve("fearless"))){
      register(command);
      assertEquals(List.of(old), FileAssociations.identities(family));
      reconcile(identity, command(), List.of());
      assertEquals(List.of(), replaced);
      assertEquals(List.of(), FileAssociations.identities(family));
    }
  }
  @Test void aReconcileWithNoExtensionsRemovesTheIdentity(){
    reconcile(identity, command(), List.of(ext, fearlessExt));
    assertEquals(List.of(identity), FileAssociations.identities(family));
    reconcile(identity, command(), List.of());
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void aPartialRegistrationIsAnIdentityAndRemovingEveryIdentityRemovesIt(){
    partial(old);
    assertEquals(List.of(old), FileAssociations.identities(family));
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void twoIdentitiesOfTheFamilyAreRefusedBeforeAnyCheckOfTheExtensions(){
    partial(old);
    partial(old+"Other");
    registered("other", ext);
    assertEquals("ambiguous "+old+"\n"+old+"Other", refused(List.of(ext), List.of()));
    assertEquals(List.of(old, old+"Other"), FileAssociations.identities(family));
  }
  @Test void anExtensionAProgramOutsideTheFamilyHoldsIsRefusedUntilTakenWhateverItsKind(){
    registered("other", ext, fearlessExt);
    assertEquals("notOurs {"+fearlessExt+"=other, "+ext+"=other}", refused(List.of(fearlessExt, ext), List.of()));
    assertEquals("notOurs {"+fearlessExt+"=other}", refused(List.of(fearlessExt, ext), List.of(ext)));
    assertEquals(List.of(), FileAssociations.identities(family));
    reconcile(identity, command(), List.of(fearlessExt, ext), List.of(ext, fearlessExt));
    assertEquals(List.of(identity), FileAssociations.identities(family));
    if (Fs.isMac()){ assertEquals(choices(identity, MacAssociations.typeOf(identity, fearlessExt), MacAssociations.typeOf(identity, ext)), choicesOfTheDesk()); }
    if (Fs.isWindows()){ Err.strCmp("[###] "+identity+ext, regOut("query", "HKCR\\"+ext, "/ve")); }
  }
  @Test void anExtensionAnotherProgramOfTheFamilyHoldsIsTakenWithNoRefusal(){
    registered(old+"Gone", ext);
    reconcile(identity, command(), List.of(ext));
    assertEquals(List.of(identity), FileAssociations.identities(family));
    if (Fs.isMac()){ assertEquals(choices(identity, MacAssociations.typeOf(identity, ext)), choicesOfTheDesk()); }
  }
  @Test void aPreferenceOfTheUserForAnotherProgramIsRefusedUntilTakenAndTakingRemovesIt(){
    reconcile(identity, command(), List.of(ext));
    preferred("other", ext);
    assertEquals("notOurs {"+ext+"=other}", refused(List.of(ext), List.of()));
    assertEquals(preference("other"), preferenceLeft(ext));
    reconcile(identity, command(), List.of(ext), List.of(ext));
    assertEquals(noPreference("other"), preferenceLeft(ext));
  }
  @Test void aPreferenceOfTheUserForAProgramOfTheFamilyIsRemovedWithNoRefusal(){
    reconcile(identity, command(), List.of(ext));
    var window= identity+"-1a2b";
    preferred(window, ext);
    assertEquals(preference(window), preferenceLeft(ext));
    reconcile(identity, command(), List.of(ext));
    assertEquals(noPreference(window), preferenceLeft(ext));
  }
  @Test void anExtensionAnotherProgramTakesBackIsHeldByTheIdentityOnceTaken(){
    reconcile(identity, command(), List.of(ext));
    if (Fs.isWindows()){ registered("other", ext); }
    if (!Fs.isWindows()){ preferred("other", ext); }
    assertEquals("notOurs {"+ext+"=other}", refused(List.of(ext), List.of()));
    reconcile(identity, command(), List.of(ext), List.of(ext));
    reconcile(identity, command(), List.of(ext));
  }
  @Test void anEntryWrittenByHandInTheRegistrationOfTheIdentityIsNoExtension(){
    reconcile(identity, command(), List.of(ext));
    if (!Fs.isWindows()){
      var file= Fs.isMac() ? MacAssociations.home.resolve(identity+".app").resolve("Contents").resolve("Info.plist") : tmp.resolve("home").resolve("applications").resolve(identity+".desktop");
      var written= Fs.readUtf8(file);
      Fs.writeUtf8(file, written+(Fs.isMac() ? "<!-- "+ext+" -->\n" : "MimeType=\n"));
      reconcile(identity, command(), List.of(ext));
      assertEquals(written, Fs.readUtf8(file));
    }
    if (Fs.isWindows()){
      var declared= hkcu+identity+"\\Capabilities\\FileAssociations";
      importReg(regKey(declared, "", identity+ext));
      reconcile(identity, command(), List.of(ext));
      Err.strCmp("[###] "+identity+ext, regOut("query", declared, "/ve"));
    }
    reconcile(identity, command(), List.of());
    assertEquals(List.of(), FileAssociations.identities(family));
  }
  @Test void aCommandOutsideAsciiReachesReplacedAsWritten(){
    var oldCommand= tmp.resolve("café 中").resolve("fearless");
    reconcile(old, oldCommand, List.of(ext));
    reconcile(identity, command(), List.of(ext));
    assertEquals(List.of(oldCommand), replaced);
  }
  @Test void removingAnIdentityKeepsTheClaimOfAnotherProgramOnTheSameExtension(){
    claim(ext);
    reconcile(identity, command(), List.of(ext));
    assertEquals(List.of(identity), FileAssociations.identities(family));
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of(), FileAssociations.identities(family));
    assertTrue(claimed(ext));
  }
}
