package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.awt.Color;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.channels.OverlappingFileLockException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.FileTime;
import java.util.ArrayList;
import java.util.Base64;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.ToIntFunction;
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
import fileAssociations.Ico;
import fileAssociations.Icon;
import fileAssociations.LinuxAssociations;
import fileAssociations.MacAssociations;
import fileAssociations.MacAssociations.Declared;
import fileAssociations.WindowIcon;
import fileAssociations.WindowsAssociations;
import tools.Fs;
import tools.OpenPath;
import utils.Err;
import utils.Push;
import utils.Range;

/// FileAssociations.reconcile on Linux, against a desktop made of the folders of a test.
/// FileAssociations.reconcile on macOS, against a folder of a test for the helper bundles and the types a test declares.
/// FileAssociations.reconcile on Windows, against keys of the registry of the current user with an identity, a family and extensions that only this test uses.
final class AssociationsTest{
  static{ Err.setUp(AssertionFailedError.class, Assertions::assertEquals, Assertions::assertTrue); }
  private static final String probe= "fearlessAssociationsProbe";
  private static final Predicate<String> family= Fs.isWindows() ? s -> s.startsWith(probe) : s -> s.contains("earless");
  private static final String identity= Fs.isWindows() ? probe+"0_001" : "fearlessManaged0_001";
  private static final String older= probe+"0_000";
  private static final Path command= Fs.isWindows() ? Path.of("C:\\Program Files\\it's here", identity+".exe") : Path.of("/opt/fearlessManaged0_001/bin/fearlessManaged0_001");
  private static final Path macCommand= Path.of("/Applications/it's here/fearlessManaged0_001.app/Contents/MacOS/fearlessManaged0_001");
  private static final Declared html= new Declared("public.html", Path.of("/System/Library/CoreServices/CoreTypes.bundle"));
  private static final Declared sketch= new Declared("com.example.sketch", Path.of("/Applications/Sketch.app"));
  private static final String user= "HKEY_CURRENT_USER\\Software\\";
  private static final String classes= user+"Classes\\";
  private static final String fileExts= user+"Microsoft\\Windows\\CurrentVersion\\Explorer\\FileExts\\";
  private static final String registeredApplications= user+"RegisteredApplications";
  private static final String machine= "HKEY_LOCAL_MACHINE\\Software\\";
  private static final List<String> winExtensions= List.of(".ffile901", ".ffile942", ".fassochtm", ".fassocqux", ".fassocprobe");
  @TempDir Path root;
  private Path home;
  private Path sys;
  private final List<List<String>> ran= new ArrayList<>();
  private final List<Path> replaced= new ArrayList<>();
  private Function<String,String> env;
  private BiConsumer<List<String>,Function<String,RuntimeException>> run;
  private final Path macHome= MacAssociations.home;
  private final Function<String,List<Declared>> declared= MacAssociations.declared;
  private final ToIntFunction<Path> register= MacAssociations.register;
  private final Function<String,Optional<Path>> holder= MacAssociations.holder;
  private final String preferences= MacAssociations.preferences;
  private final List<String> reload= MacAssociations.reload;
  private final Runnable notifyShell= WindowsAssociations.notifyShell;
  private final Map<String,List<Declared>> types= new HashMap<>();
  private final Map<String,Path> holders= new HashMap<>();
  private final List<Path> registered= new ArrayList<>();
  private final Path lockFolder= FileAssociations.lockFolder;
  @BeforeEach void desktop(){
    FileAssociations.lockFolder = root.resolve("data");
    if (Fs.isWindows()){ cleanUp(); WindowsAssociations.notifyShell = () -> ran.add(List.of("SHChangeNotify")); return; }
    if (Fs.isMac()){ macDesktop(); return; }
    home = root.resolve("home");
    sys = root.resolve("sys");
    env = LinuxAssociations.env;
    run = LinuxAssociations.run;
    var vars= Map.of("XDG_DATA_HOME", home.toString(), "XDG_DATA_DIRS", sys.toString(),
      "XDG_CONFIG_HOME", root.resolve("config").toString(), "XDG_CONFIG_DIRS", root.resolve("etc").toString(), "XDG_CURRENT_DESKTOP", "");
    LinuxAssociations.env = vars::get;
    LinuxAssociations.run = (cmd,_) -> ran.add(cmd);
    Fs.writeUtf8(sys.resolve("mime").resolve("globs2"), """
# This file was automatically generated by the
# update-mime-database command. DO NOT EDIT!
80:text/html:*.htm
80:text/html:*.html
50:application/xhtml+xml:*.htm
50:text/plain:*.txt
50:text/x-bar:*.BAR
50:text/x-csrc:*.c:cs
50:text/x-c++src:*.C:cs
""");
  }
  private void macDesktop(){
    MacAssociations.home = Fs.of(root::toRealPath).resolve("home");
    MacAssociations.declared = e -> types.getOrDefault(e, List.of());
    MacAssociations.register = b -> { registered.add(b); return 0; };
    MacAssociations.holder = e -> Optional.ofNullable(holders.get(e));
    MacAssociations.preferences = "fearless_test_"+root.getFileName();
    MacAssociations.reload = List.of("touch", root.resolve("reloaded").toString());
  }
  @AfterEach void restore(){
    desktopRestored();
    FileAssociations.lockFolder = lockFolder;
  }
  private void desktopRestored(){
    if (Fs.isWindows()){ cleanUp(); WindowsAssociations.notifyShell = notifyShell; return; }
    if (Fs.isMac()){ macRestore(); return; }
    LinuxAssociations.env = env;
    LinuxAssociations.run = run;
  }
  private void macRestore(){
    MacAssociations.home = macHome;
    MacAssociations.declared = declared;
    MacAssociations.register = register;
    MacAssociations.holder = holder;
    ReconcileTest.defaults("delete", MacAssociations.preferences);
    Fs.ofV(() -> Files.deleteIfExists(preferencesFile()));
    MacAssociations.preferences = preferences;
    MacAssociations.reload = reload;
  }
  private static void cleanUp(){
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    for (var e : winExtensions){
      reg("delete", classes+e, "/f");
      reg("delete", classes+"otherProgram"+e, "/f");
      reg("delete", fileExts+e, "/f");
    }
    reg("delete", user+identity, "/f");
  }
  private static Optional<String> reg(String... args){
    var p= Fs.of(new ProcessBuilder(Push.of("reg", List.of(args))).redirectErrorStream(true)::start);
    var out= new String(Fs.of(() -> p.getInputStream().readAllBytes()), StandardCharsets.UTF_8);
    return p.onExit().join().exitValue() == 0 ? Optional.of(out) : Optional.empty();
  }
  private static boolean exists(String key){ return reg("query", key).isPresent(); }
  private static String data(String line){
    var end= line.indexOf(' ', line.indexOf("    REG_") + 4);
    return end < 0 ? "" : line.substring(end).strip();
  }
  private static Map<String,String> values(String key){
    var res= new LinkedHashMap<String,String>();
    reg("query", key).orElse("").lines().filter(l -> l.contains("    REG_")).forEach(l -> res.put(l.substring(0, l.indexOf("    REG_")).strip(), data(l)));
    return res;
  }
  private static Optional<String> value(String key, String name){
    var found= name.isEmpty() ? reg("query", key, "/ve") : reg("query", key, "/v", name);
    return found.flatMap(out -> out.lines().filter(l -> l.contains("    REG_")).findFirst()).map(AssociationsTest::data);
  }
  private static String regKey(String key, String name, String data){
    var shown= name.isEmpty() ? "@" : "\""+name+"\"";
    return "\r\n["+key+"]\r\n"+shown+"=\""+data.replace("\\", "\\\\").replace("\"", "\\\"")+"\"\r\n";
  }
  private boolean imported(String keys){
    var text= "\uFEFFWindows Registry Editor Version 5.00\r\n"+keys;
    var bytes= new byte[2*text.length()];
    for (int i : Range.of(0, text.length())){ bytes[2*i] = (byte)text.charAt(i); bytes[2*i+1] = (byte)(text.charAt(i) >> 8); }
    var file= root.resolve("keys.reg");
    Fs.ofV(() -> Files.write(file, bytes));
    return reg("import", file.toString()).isPresent();
  }
  private void importReg(String keys){ assertTrue(imported(keys), keys); }
  private static void deny(String key, String rights){ permission(key, rights, "AddAccessRule"); }
  private static void permit(String key, String rights){ permission(key, rights, "RemoveAccessRule"); }
  private static void permission(String key, String rights, String change){
    var script= "$ErrorActionPreference='Stop';"
      +"$k=[Microsoft.Win32.Registry]::CurrentUser.OpenSubKey('"+key.substring("HKEY_CURRENT_USER\\".length())+"','ReadWriteSubTree','ChangePermissions,ReadPermissions');"
      +"$a=$k.GetAccessControl();"
      +"[void]$a."+change+"((New-Object Security.AccessControl.RegistryAccessRule([Security.Principal.WindowsIdentity]::GetCurrent().User,'"+rights+"','Deny')));"
      +"$k.SetAccessControl($a)";
    var encoded= Base64.getEncoder().encodeToString(script.getBytes(StandardCharsets.UTF_16LE));
    var p= Fs.of(new ProcessBuilder("powershell", "-NoProfile", "-NonInteractive", "-EncodedCommand", encoded).redirectErrorStream(true)::start);
    var out= new String(Fs.of(() -> p.getInputStream().readAllBytes()), StandardCharsets.UTF_8);
    assertEquals(0, p.onExit().join().exitValue(), out);
  }
  private AutoCloseable aside(String key){
    var file= root.resolve(key.hashCode()+".reg");
    var kept= reg("export", key, file.toString(), "/y").isPresent();
    reg("delete", key, "/f");
    return () -> { reg("delete", key, "/f"); if (kept){ assertTrue(reg("import", file.toString()).isPresent()); } };
  }
  private static final String needsAdmin= "This test writes keys of HKEY_LOCAL_MACHINE with \"reg import\": it needs an administrator on this desk.";
  private AutoCloseable allUsers(String name){
    var progId= name+".ffile901";
    var keys= regKey(machine+name+"\\Capabilities\\FileAssociations", ".ffile901", progId)
      +regKey(machine+"Classes\\"+progId+"\\shell\\open\\command", "", "\"C:\\Program Files\\"+name+".exe\" \"%1\"")
      +regKey(machine+"RegisteredApplications", name, "Software\\"+name+"\\Capabilities");
    assertTrue(imported(keys), needsAdmin);
    return () -> {
      reg("delete", machine+name, "/f");
      reg("delete", machine+"Classes\\"+progId, "/f");
      reg("delete", machine+"RegisteredApplications", "/v", name, "/f");
    };
  }
  private Path icon(int rgb){
    var file= root.resolve("in").resolve(Integer.toHexString(rgb)+".png");
    var img= new BufferedImage(64, 64, BufferedImage.TYPE_INT_RGB);
    var g= img.createGraphics();
    g.setColor(new Color(rgb));
    g.fillRect(0, 0, 64, 64);
    g.dispose();
    Fs.ensureDir(file.getParent());
    Fs.ofV(() -> ImageIO.write(img, "png", file.toFile()));
    return file;
  }
  private void reconcile(String... extensions){ taking(List.of(), extensions); }
  private void taking(List<String> taken, String... extensions){ reconcile(identity, List.of(), taken, extensions); }
  private void reconcile(List<WindowIcon> windows, String... extensions){ reconcile(identity, windows, List.of(), extensions); }
  private void reconcile(String identity, List<WindowIcon> windows, List<String> taken, String... extensions){
    reconcile(identity, windows, taken, Stream.of(extensions).map(e -> { var png= icon(e.hashCode() & 0xffffff); return new Icon(e, png, png); }).toList());
  }
  private void reconcile(List<Icon> icons){ reconcile(identity, List.of(), List.of(), icons); }
  private void reconcile(String identity, List<WindowIcon> windows, List<String> taken, List<Icon> icons){
    var program= icon(0x123456);
    FileAssociations.reconcile(identity, "Fearless Manager", family, Fs.isMac() ? macCommand : command, icons, taken, windows, program, replaced::add,
      s -> new IllegalStateException("ambiguous "+s),
      s -> new IllegalStateException("notOurs "+s),
      s -> new IllegalStateException("notTaken "+s),
      s -> new IllegalStateException("notWritable "+s),
      s -> new IllegalStateException("halfDone "+s));
  }
  private String refused(String... extensions){ return assertThrows(IllegalStateException.class, () -> reconcile(extensions)).getMessage(); }
  private String refusedTaking(List<String> taken, String... extensions){ return assertThrows(IllegalStateException.class, () -> taking(taken, extensions)).getMessage(); }
  private Path mimetypes(){ return home.resolve("icons").resolve("hicolor").resolve("256x256").resolve("mimetypes"); }
  private Path appIcon(){ return home.resolve("icons").resolve("hicolor").resolve("256x256").resolve("apps").resolve(identity+".png"); }
  private Path desktopFile(){ return home.resolve("applications").resolve(identity+".desktop"); }
  private Path packageFile(){ return home.resolve("mime").resolve("packages").resolve(identity+".xml"); }
  private String mimeTypes(){ return Fs.readUtf8(desktopFile()).lines().filter(l -> l.startsWith("MimeType=")).findFirst().orElseThrow(); }
  private List<String> icons(){
    if (!Files.isDirectory(mimetypes())){ return List.of(); }
    return Fs.of(() -> { try (var s= Files.list(mimetypes())){ return s.map(p -> p.getFileName().toString()).sorted().toList(); }});
  }
  private List<List<String>> rebuilt(){
    if (Fs.isWindows()){ return List.of(List.of("SHChangeNotify")); }
    return List.of(List.of("update-mime-database", home.resolve("mime").toString()), List.of("update-desktop-database", home.resolve("applications").toString()));
  }
  private String mimeInfo(String... types){
    return """
<?xml version="1.0" encoding="UTF-8"?>
<mime-info xmlns="http://www.freedesktop.org/standards/shared-mime-info">
"""+Stream.of(types).map(t -> "  <mime-type type=\"application/x-fearless"+t+"<icon name=\"fearlessManaged0_001-[###]\"/></mime-type>\n").collect(Collectors.joining())+"</mime-info>\n";
  }
  private void sysMime(String file, String text){
    var path= sys.resolve("mime").resolve(file);
    Fs.writeUtf8(path, (Files.exists(path) ? Fs.readUtf8(path) : "")+text);
  }
  private List<String> windowEntries(){
    return Fs.of(() -> { try (var s= Files.list(home.resolve("applications"))){ return s.map(p -> p.getFileName().toString()).filter(n -> !n.equals(identity+".desktop")).sorted().toList(); }});
  }
  private static Path preferencesFile(){ return Path.of(System.getProperty("user.home"), "Library", "Preferences", MacAssociations.preferences+".plist"); }
  private static void withReadOnly(Path p, Runnable body){
    assertTrue(p.toFile().setWritable(false));
    try{
      assertFalse(Files.isWritable(p), "This test needs a user that the permission denies: run the tests as a normal user, not as root.");
      body.run();
    }
    finally{ p.toFile().setWritable(true); }
  }
  private static final String unreadableExported= "<dict><key>UTTypeIdentifier</key><string>com.example.ffile996</string><key>UTTypeConformsTo</key><array><string>public.data</string></array>"
    +"<key>UTTypeTagSpecification</key><dict><key>public.filename-extension</key><array><string>ffile996</string></array></dict></dict>\n";
  private static String choices(String... types){ return ReconcileTest.choices("fearlessManaged0-001", types); }
  private Path bundle(){ return MacAssociations.home.resolve(identity+".app"); }
  private Path contents(String file){ return bundle().resolve("Contents").resolve(file); }
  private List<String> files(){ return Fs.walk(bundle(), s -> s.filter(Files::isRegularFile).map(f -> bundle().relativize(f).toString()).sorted().toList()); }
  private String icns(String ext){
    var image= Ico.png(icon(("."+ext).hashCode() & 0xffffff));
    var bytes= ByteBuffer.allocate(16 + image.length).put("icns".getBytes(StandardCharsets.UTF_8)).putInt(16 + image.length).put("ic08".getBytes(StandardCharsets.UTF_8)).putInt(8 + image.length).put(image).array();
    return LinuxAssociations.hash(bytes)+".icns";
  }
  private List<String> bundleFiles(String... icns){
    return Stream.concat(Stream.of("Contents/Info.plist", "Contents/MacOS/fearlessManaged0_001", "Contents/Resources/_program.icns", "Contents/Resources/en.lproj/InfoPlist.strings"), Stream.of(icns).map(i -> "Contents/Resources/"+i)).sorted().toList();
  }
  private String document(String ext, String rank, String type){
    return "<dict><key>CFBundleTypeRole</key><string>Viewer</string>"
      +"<key>CFBundleTypeIconFile</key><string>"+icns(ext)+"</string><key>LSHandlerRank</key><string>"+rank+"</string>"
      +"<key>LSItemContentTypes</key><array><string>"+type+"</string></array></dict>\n";
  }
  private String exported(String ext){
    return "<dict><key>UTTypeIdentifier</key><string>fearlessmanaged0-001."+ext+"</string>"
      +"<key>UTTypeIconFile</key><string>"+icns(ext)+"</string><key>UTTypeConformsTo</key><array><string>public.data</string></array>"
      +"<key>UTTypeTagSpecification</key><dict><key>public.filename-extension</key><array><string>"+ext+"</string></array></dict></dict>\n";
  }
  private void plistIs(String documents, String exported){ assertEquals(MacAssociations.plist(identity, "Fearless Manager", documents, exported), Fs.readUtf8(contents("Info.plist"))); }
  @Test void anExtensionNoProgramDeclaresGetsATypeOfTheIdentity(){
    if (Fs.isWindows()){
      reconcile(".ffile901");
      var progId= identity+".ffile901";
      assertEquals(Optional.of(progId), value(classes+".ffile901", ""));
      assertEquals(Map.of(progId, ""), values(classes+".ffile901\\OpenWithProgids"));
      assertEquals(Map.of(".ffile901", progId), values(user+identity+"\\Capabilities\\FileAssociations"));
      assertEquals(Optional.of("Software\\"+identity+"\\Capabilities"), value(registeredApplications, identity));
      assertEquals(rebuilt(), ran);
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      Err.strCmp("""
  <?xml version="1.0" encoding="UTF-8"?>
  <!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
  <plist version="1.0"><dict>
  <key>CFBundleExecutable</key><string>fearlessManaged0_001</string>
  <key>CFBundleIdentifier</key><string>fearlessManaged0-001</string>
  <key>CFBundleName</key><string>Fearless Manager</string>
  <key>CFBundleDisplayName</key><string>fearlessManaged0_001</string>
  <key>CFBundlePackageType</key><string>APPL</string>
  <key>CFBundleIconFile</key><string>_program.icns</string>
  <key>CFBundleVersion</key><string>1</string>
  <key>CFBundleDocumentTypes</key><array>
  """+document("fapp123", "Owner", "fearlessmanaged0-001.fapp123")+"""
  </array>
  <key>UTExportedTypeDeclarations</key><array>
  """+exported("fapp123")+"""
  </array>
  </dict></plist>
  """, Fs.readUtf8(contents("Info.plist")));
      assertEquals(bundleFiles(icns("fapp123")), files());
      assertEquals("CFBundleDisplayName = \"Fearless Manager\";\n", Fs.readUtf8(contents("Resources/en.lproj/InfoPlist.strings")));
      assertEquals(List.of(bundle()), registered);
      assertFalse(Files.exists(root.resolve("reloaded")));
      return;
    }
    reconcile(".ffile001");
    Err.strCmp(mimeInfo("-ffile001\"><glob pattern=\"*.ffile001\" weight=\"100\"/>"), Fs.readUtf8(packageFile()));
    assertEquals("MimeType=application/x-fearless-ffile001;", mimeTypes());
    assertEquals(1, icons().size());
    assertEquals(rebuilt(), ran);
  }
  @Test void theProgramOfTheIdentityRunsTheCommandOnTheOpenedFile(){
    if (Fs.isWindows()){
      reconcile(".ffile901");
      assertEquals(Optional.of("\"C:\\Program Files\\it's here\\"+identity+".exe\" \"%1\""), value(classes+identity+".ffile901\\shell\\open\\command", ""));
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      assertEquals("#!/bin/sh\nexec '/Applications/it'\\''s here/fearlessManaged0_001.app/Contents/MacOS/fearlessManaged0_001' FearlessCommandOpened\n", Fs.readUtf8(contents("MacOS/"+identity)));
      assertEquals(true, Files.isExecutable(contents("MacOS/"+identity)));
      return;
    }
    reconcile(".ffile001");
    var lines= Fs.readUtf8(desktopFile()).lines().filter(l -> l.startsWith("Exec=") || l.startsWith("TryExec=")).toList();
    assertEquals(List.of("Exec=env LC_ALL=C.UTF-8 \"/opt/fearlessManaged0_001/bin/fearlessManaged0_001\" %f", "TryExec=/opt/fearlessManaged0_001/bin/fearlessManaged0_001"), lines);
  }
  private static String launchServices(String question, Path path){
    var p= Fs.of(new ProcessBuilder("osascript", "-l", "JavaScript", "-e", "function run(a){ ObjC.import('AppKit'); "+question+" }", path.toString())::start);
    return new String(Fs.of(p.getInputStream()::readAllBytes), StandardCharsets.UTF_8).strip();
  }
  @Test void theDesktopKnowsTheTypeOfTheIdentityUntilTheIdentityIsRemoved(){
    if (Fs.isWindows()){
      var file= root.resolve("a.fassocprobe");
      assertTrue(OpenPath.noProgramOpens(file));
      reconcile(".fassocprobe");
      assertFalse(OpenPath.noProgramOpens(file));
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertTrue(OpenPath.noProgramOpens(file));
      return;
    }
    if (Fs.isMac()){
      MacAssociations.declared = declared;
      MacAssociations.register = register;
      var probe= MacAssociations.home.resolve("fearlessAssociationsTestProbe.app");
      assertEquals(html, declared.apply("htm").getFirst());
      reconcile("fearlessAssociationsTestProbe", List.of(), List.of(), ".fcommonsprobe");
      assertEquals(List.of(new Declared("fearlessassociationstestprobe.fcommonsprobe", probe)), declared.apply("fcommonsprobe"));
      var file= root.resolve("x.fcommonsprobe");
      Fs.writeUtf8(file, "x");
      assertEquals("Fearless Manager", launchServices("return ObjC.unwrap($.NSFileManager.defaultManager.displayNameAtPath(a[0]))", probe));
      var kind= launchServices("var k= Ref(); $.NSURL.fileURLWithPath(a[0]).getResourceValueForKeyError(k, $.NSURLLocalizedTypeDescriptionKey, null); return ObjC.unwrap(k[0])", file);
      assertFalse(kind.isEmpty() || kind.contains("fearlessAssociationsTestProbe"), kind);
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertEquals(List.of(), declared.apply("fcommonsprobe"));
      assertFalse(Files.exists(probe));
      assertEquals(0, Fs.of(new ProcessBuilder("/System/Library/Frameworks/CoreServices.framework/Frameworks/LaunchServices.framework/Support/lsregister", "-u", probe.toString()).inheritIO()::start).onExit().join().exitValue());
      return;
    }
    LinuxAssociations.run = run;
    var globs= home.resolve("mime").resolve("globs2");
    reconcile(".fcommonsprobe");
    Err.strCmp("[###]application/x-fearless-fcommonsprobe:*.fcommonsprobe[###]", Fs.readUtf8(globs));
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertFalse(Fs.readUtf8(globs).contains("application/x-fearless-fcommonsprobe"));
  }
  @Test void aSystemExtensionIsOpenedBelowEveryTypeTheSystemGivesIt(){
    if (Fs.isWindows()){
      importReg(regKey(classes+".fassochtm", "", "otherProgram.fassochtm"));
      taking(List.of(".fassochtm"), ".fassochtm");
      assertEquals(Optional.of(identity+".fassochtm"), value(classes+".fassochtm", ""));
      assertEquals(Optional.of("otherProgram.fassochtm"), value(user+identity+"\\PreviousDefaults", ".fassochtm"));
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertEquals(Optional.of("otherProgram.fassochtm"), value(classes+".fassochtm", ""));
      return;
    }
    if (Fs.isMac()){
      types.put("htm", List.of(html));
      reconcile(".htm", ".fapp123");
      plistIs(document("htm", "Alternate", "public.html")+document("fapp123", "Owner", "fearlessmanaged0-001.fapp123"), exported("fapp123"));
      assertFalse(Files.exists(preferencesFile()));
      return;
    }
    reconcile(".htm");
    Err.strCmp(mimeInfo("-htm\"><glob pattern=\"*.htm\" weight=\"100\"/><sub-class-of type=\"text/html\"/><sub-class-of type=\"application/xhtml+xml\"/>"), Fs.readUtf8(packageFile()));
    assertEquals("MimeType=application/x-fearless-htm;", mimeTypes());
    assertEquals(1, icons().size());
    assertTrue(Files.isRegularFile(appIcon()));
    assertEquals(rebuilt(), ran);
  }
  @Test void theProgramOpeningTheSystemTypeOfASystemExtensionHoldsItUntilTaken(){
    if (Fs.isWindows()){
      importReg(regKey(classes+".fassochtm", "", "otherProgram.fassochtm")+regKey(classes+".fassochtm\\OpenWithProgids", "otherProgram.fassochtm", ""));
      assertEquals("notOurs {.fassochtm=otherProgram}", refused(".fassochtm"));
      assertEquals(List.of(), FileAssociations.identities(family));
      taking(List.of(".fassochtm"), ".fassochtm");
      assertEquals(Optional.of(identity+".fassochtm"), value(classes+".fassochtm", ""));
      assertEquals(Map.of("otherProgram.fassochtm", "", identity+".fassochtm", ""), values(classes+".fassochtm\\OpenWithProgids"));
      return;
    }
    if (Fs.isMac()){
      types.put("htm", List.of(html));
      holders.put(".htm", Path.of("/Applications/Browser.app"));
      assertEquals("notOurs {.htm=Browser}", refused(".htm"));
      assertFalse(Files.exists(bundle()));
      taking(List.of(".htm"), ".htm");
      plistIs(document("htm", "Alternate", "public.html"), "");
      assertEquals(choices("public.html"), ReconcileTest.choicesOfTheDesk());
      assertTrue(Files.exists(root.resolve("reloaded")));
      return;
    }
    Fs.writeUtf8(sys.resolve("applications").resolve("browser.desktop"), "[Desktop Entry]\nMimeType=text/html;application/xhtml+xml;\n");
    Fs.writeUtf8(root.resolve("config").resolve("mimeapps.list"), "[Default Applications]\ntext/html=browser.desktop\n[Added Associations]\ntext/html=browser.desktop;\n");
    assertEquals("notOurs {.htm=browser}", refused(".htm"));
    assertFalse(Files.exists(home));
    taking(List.of(".htm"), ".htm");
    assertEquals("MimeType=application/x-fearless-htm;", mimeTypes());
    assertEquals("[Default Applications]\ntext/html=browser.desktop\n[Added Associations]\ntext/html=browser.desktop;\n", Fs.readUtf8(root.resolve("config").resolve("mimeapps.list")));
  }
  @Test void aTypeWithNoProgramOfItsOwnIsHeldByTheProgramOfItsNearestParentType(){
    if (Fs.isMac()){ fail("""
      Agent on macOS: on Linux an extension whose type no program opens is held by the program of the nearest parent type of that type (the file subclasses of the MIME database).
      On macOS a type conforms to other types (UTTypeConformsTo), and MacAssociations.holder asks LaunchServices which application opens a file named x<ext>.
      Find on this desk an extension whose type no application opens as its own type, while an application opens a type it conforms to (for example .log, public.log, conforming to public.plain-text).
      Make the macOS form check, with the real MacAssociations.holder, that reconcile refuses that extension with notOurs naming that application until the extension is taken."""); }
    if (Fs.isWindows()){ fail("""
      Agent on Windows: on Linux an extension whose type no program opens is held by the program of the nearest parent type of that type (the file subclasses of the MIME database).
      On Windows an extension with no ProgId of its own can still be opened through its PerceivedType (Classes\\SystemFileAssociations\\<perceived type>) or through Classes\\*.
      Investigate whether Explorer opens a file of a test extension holding only PerceivedType=text with a program, and whether WindowsAssociations sees that program as the holder.
      Make the Windows form check that reconcile refuses that extension with notOurs naming that program until the extension is taken,
      or say in ReconciliatorDesign why such an extension has no holder on Windows, and make the Windows form check that reconcile takes that extension with no refusal."""); }
    sysMime("globs2", "50:text/markdown:*.md\n50:text/x-log:*.log\n");
    sysMime("subclasses", "text/markdown text/plain\ntext/x-doc text/plain\ntext/x-log text/x-doc\n");
    Fs.writeUtf8(sys.resolve("applications").resolve("editor.desktop"), "[Desktop Entry]\nMimeType=text/plain;\n");
    Fs.writeUtf8(sys.resolve("applications").resolve("reader.desktop"), "[Desktop Entry]\nMimeType=text/x-doc;\n");
    Fs.writeUtf8(root.resolve("config").resolve("mimeapps.list"), "[Default Applications]\ntext/x-log=viewer.desktop\n");
    assertEquals("notOurs {.md=editor, .log=reader}", refused(".md", ".log"));
    Fs.writeUtf8(sys.resolve("applications").resolve("viewer.desktop"), "[Desktop Entry]\n");
    assertEquals("notOurs {.md=editor, .log=viewer}", refused(".md", ".log"));
    assertFalse(Files.exists(home));
    taking(List.of(".md"), ".md");
    Fs.writeUtf8(home.resolve("mime").resolve("globs2"), "100:application/x-fearless-md:*.md\n");
    Fs.writeUtf8(home.resolve("mime").resolve("subclasses"), "application/x-fearless-md text/markdown\n");
    reconcile(".md");
  }
  @Test void aProgramRemovedFromATypeOfTheIdentityLeavesTheExtensionToTheProgramOfTheParentType(){
    if (Fs.isMac()){ fail("""
      Agent on macOS: on Linux the user can remove the program of the identity from a type of the identity ([Removed Associations] of mimeapps.list);
      the extension of that type then opens with the program of the parent type, which holds the extension until the extension is taken, and taking it removes that line.
      Find whether the user can do the same on macOS to a type the helper bundle opens as owner, other than the choice in LSHandlers that aPreferenceForATypeOfTheIdentityIsRemovedFromEveryListOnlyWhenEveryHeldExtensionIsTaken checks.
      Make the macOS form check that change, or say in ReconciliatorDesign that on macOS that choice is the only way, and make the macOS form check that taking the extension removes a choice in LSHandlers of a type the helper bundle opens as alternate."""); }
    if (Fs.isWindows()){ fail("""
      Agent on Windows: on Linux the user can remove the program of the identity from a type of the identity ([Removed Associations] of mimeapps.list);
      the extension of that type then opens with the program of the parent type, which holds the extension until the extension is taken, and taking it removes that line.
      On Windows the user removes a program from the "Open with" choices of an extension through FileExts\\<ext>\\OpenWithProgids and FileExts\\<ext>\\OpenWithList.
      Investigate which program holds a test extension after the user removes the ProgId of the identity there, and make the Windows form check that reconcile refuses that extension until the extension is taken,
      and what taking the extension changes in those keys."""); }
    typesOfTheIdentity(".htm");
    Fs.writeUtf8(home.resolve("mime").resolve("subclasses"), "application/x-fearless-htm text/html\n");
    var config= root.resolve("config").resolve("mimeapps.list");
    Fs.writeUtf8(config, "[Added Associations]\napplication/x-fearless-htm=fearlessManaged0_001.desktop;\n[Removed Associations]\napplication/x-fearless-htm=fearlessManaged0_001.desktop;\n");
    assertEquals("notOurs {.htm=browser}", refused(".htm"));
    taking(List.of(".htm"), ".htm");
    assertEquals("[Added Associations]\n[Removed Associations]\n", Fs.readUtf8(config));
    reconcile(".htm");
  }
  @Test void anEntryOfTheUserHidesTheTypesOfTheEntryOfTheSameNameInTheSystem(){
    if (Fs.isMac()){ fail("""
      Agent on macOS: on Linux the .desktop file of a program in the folder of the user hides the .desktop file of the same name in a folder of the system, with the types that file lists.
      On macOS two applications can have the same CFBundleIdentifier, one in ~/Applications and one in /Applications, declaring different types.
      Investigate which of the two LaunchServices uses for MacAssociations.declared and MacAssociations.holder, and make the macOS form check that reconcile follows the types of that application,
      or say in ReconciliatorDesign why macOS has no such case, and make the macOS form check what reconcile does with the two applications."""); }
    if (Fs.isWindows()){ fail("""
      Agent on Windows: on Linux the .desktop file of a program in the folder of the user hides the .desktop file of the same name in a folder of the system, with the types that file lists.
      On Windows HKEY_CLASSES_ROOT shows the key Software\\Classes\\<name> of HKEY_CURRENT_USER in place of the key of the same name of HKEY_LOCAL_MACHINE.
      Write in HKEY_LOCAL_MACHINE\\Software\\Classes a test extension naming the ProgId of another program, and in HKEY_CURRENT_USER\\Software\\Classes a key of the same name naming no program (as allUsers does, with an administrator),
      and make the Windows form check that reconcile reads that extension as HKEY_CLASSES_ROOT shows it."""); }
    sysMime("globs2", "50:text/markdown:*.md\n");
    Fs.writeUtf8(sys.resolve("applications").resolve("editor.desktop"), "[Desktop Entry]\nMimeType=text/markdown;\n");
    assertEquals("notOurs {.md=editor}", refused(".md"));
    Fs.writeUtf8(home.resolve("applications").resolve("editor.desktop"), "[Desktop Entry]\nMimeType=text/plain;\n");
    reconcile(".md");
    assertEquals("MimeType=application/x-fearless-md;", mimeTypes());
  }
  private void typesOfTheIdentity(String... extensions){
    reconcile(extensions);
    Fs.writeUtf8(home.resolve("mime").resolve("globs2"), String.join("", Stream.of(extensions).map(e -> "100:"+LinuxAssociations.typeOf(e)+":*"+e+"\n").toList()));
    Fs.writeUtf8(sys.resolve("applications").resolve("browser.desktop"), "[Desktop Entry]\nMimeType=text/html;\n");
    ran.clear();
  }
  @Test void aPreferenceForATypeOfTheIdentityIsRemovedFromEveryListOnlyWhenEveryHeldExtensionIsTaken(){
    if (Fs.isWindows()){
      reconcile(".fassochtm", ".fassocqux");
      importReg(regKey(fileExts+".fassochtm\\UserChoice", "ProgId", "otherProgram.fassochtm")
        +regKey(fileExts+".fassocqux\\UserChoiceLatest\\ProgId", "ProgId", "browser.fassocqux"));
      var written= reg("query", user+identity, "/s").orElseThrow();
      ran.clear();
      assertEquals("notOurs {.fassochtm=otherProgram, .fassocqux=browser}", refused(".fassochtm", ".fassocqux"));
      assertEquals("notOurs {.fassocqux=browser}", refusedTaking(List.of(".fassochtm"), ".fassochtm", ".fassocqux"));
      assertTrue(exists(fileExts+".fassochtm\\UserChoice"));
      assertEquals(written, reg("query", user+identity, "/s").orElseThrow());
      assertEquals(List.of(), ran);
      taking(List.of(".fassochtm", ".fassocqux"), ".fassochtm", ".fassocqux");
      assertFalse(exists(fileExts+".fassochtm\\UserChoice"));
      assertFalse(exists(fileExts+".fassocqux\\UserChoiceLatest"));
      assertEquals(rebuilt(), ran);
      return;
    }
    if (Fs.isMac()){
      reconcile(".htm", ".txt");
      holders.put(".htm", Path.of("/Applications/Browser.app"));
      holders.put(".txt", Path.of("/Applications/Browser.app"));
      assertEquals("notOurs {.htm=Browser, .txt=Browser}", refused(".htm", ".txt"));
      assertEquals("notOurs {.txt=Browser}", refusedTaking(List.of(".htm"), ".htm", ".txt"));
      assertFalse(Files.exists(preferencesFile()));
      taking(List.of(".htm", ".txt"), ".htm", ".txt");
      assertEquals(choices("fearlessmanaged0-001.htm", "fearlessmanaged0-001.txt"), ReconcileTest.choicesOfTheDesk());
      return;
    }
    typesOfTheIdentity(".htm", ".txt");
    var config= root.resolve("config").resolve("mimeapps.list");
    var etc= root.resolve("etc").resolve("mimeapps.list");
    var text= "[Default Applications]\ntext/html=browser.desktop\napplication/x-fearless-htm=browser.desktop\n"
      +"[Added Associations]\napplication/x-fearless-htm=editor.desktop;\n# application/x-fearless-htm=editor.desktop;\n[Removed Associations]\napplication/x-fearless-txt=browser.desktop;\n";
    Fs.writeUtf8(config, text);
    Fs.writeUtf8(etc, "[Default Applications]\n application/x-fearless-txt = browser.desktop\n");
    assertEquals("notOurs {.htm=browser, .txt=browser}", refused(".htm", ".txt"));
    assertEquals("notOurs {.txt=browser}", refusedTaking(List.of(".htm"), ".htm", ".txt"));
    assertEquals(text, Fs.readUtf8(config));
    assertEquals(List.of(), ran);
    taking(List.of(".htm", ".txt"), ".htm", ".txt");
    assertEquals("[Default Applications]\ntext/html=browser.desktop\n[Added Associations]\n# application/x-fearless-htm=editor.desktop;\n[Removed Associations]\n", Fs.readUtf8(config));
    assertEquals("[Default Applications]\n", Fs.readUtf8(etc));
    assertEquals(rebuilt(), ran);
  }
  @Test void takingAnExtensionChangesThePreferencesWhereTheDeskReadsThem(){
    if (Fs.isWindows()){
      var choice= fileExts+".ffile901\\UserChoice";
      importReg(regKey(choice, "ProgId", "otherProgram.ffile901")
        +regKey(fileExts+".ffile901\\UserChoiceLatest\\ProgId", "ProgId", "otherProgram.ffile901")
        +regKey(fileExts+".ffile901\\OpenWithList", "a", "otherProgram.exe")
        +regKey(fileExts+".ffile901\\OpenWithProgids", "otherProgram.ffile901", ""));
      deny(choice, "SetValue");
      try{ taking(List.of(".ffile901"), ".ffile901"); }
      finally{ if (exists(choice)){ permit(choice, "SetValue"); } }
      assertFalse(exists(choice));
      assertFalse(exists(fileExts+".ffile901\\UserChoiceLatest"));
      assertEquals(Map.of("a", "otherProgram.exe"), values(fileExts+".ffile901\\OpenWithList"));
      assertEquals(Map.of("otherProgram.ffile901", ""), values(fileExts+".ffile901\\OpenWithProgids"));
      reconcile(".ffile901");
      return;
    }
    if (Fs.isMac()){
      types.put("htm", List.of(html));
      reconcile(".htm");
      holders.put(".htm", Path.of("/Applications/Browser.app"));
      ReconcileTest.pick("public.plain-text", "other");
      ReconcileTest.pick("PUBLIC.HTML", "other");
      MacAssociations.register = b -> { assertTrue(Files.exists(root.resolve("reloaded"))); registered.add(b); return 0; };
      taking(List.of(".htm"), ".htm");
      Err.strCmp("[{\"LSHandlerContentType\":\"public.plain-text\",\"LSHandlerRoleAll\":\"other\"},"+choices("public.html").substring(1), ReconcileTest.choicesOfTheDesk());
      assertEquals(List.of(bundle(), bundle()), registered);
      return;
    }
    typesOfTheIdentity(".htm");
    var kept= root.resolve("kept").resolve("mimeapps.list");
    var link= root.resolve("config").resolve("mimeapps.list");
    Fs.writeUtf8(kept, "[Default Applications]\ntext/html=browser.desktop\napplication/x-fearless-htm=browser.desktop\n");
    Fs.ensureDir(link.getParent());
    Fs.ofV(() -> Files.createSymbolicLink(link, kept));
    taking(List.of(".htm"), ".htm");
    assertEquals("[Default Applications]\ntext/html=browser.desktop\n", Fs.readUtf8(kept));
    assertTrue(Files.isSymbolicLink(link));
    reconcile(".htm");
  }
  @Test void aPreferenceTheUserCanNotChangeIsRefusedBeforeWritingAnything(){
    if (Fs.isWindows()){
      var free= fileExts+".ffile901\\UserChoice";
      var locked= fileExts+".ffile942\\UserChoice";
      importReg(regKey(free, "ProgId", "otherProgram.ffile901")+regKey(locked, "ProgId", "otherProgram.ffile942"));
      deny(locked, "Delete");
      try{ assertEquals("notTaken {.ffile942="+locked+"}", refusedTaking(List.of(".ffile901", ".ffile942"), ".ffile901", ".ffile942")); }
      finally{ permit(locked, "Delete"); }
      assertTrue(exists(free));
      assertTrue(exists(locked));
      assertEquals(List.of(), FileAssociations.identities(family));
      assertEquals(List.of(), ran);
      return;
    }
    if (Fs.isMac()){
      types.put("htm", List.of(html));
      holders.put(".htm", Path.of("/Applications/Browser.app"));
      ReconcileTest.pick("public.html", "other");
      var before= ReconcileTest.choicesOfTheDesk();
      withReadOnly(preferencesFile(), () -> assertEquals("notTaken {.htm="+preferencesFile()+"}", refusedTaking(List.of(".htm"), ".htm")));
      assertEquals(before, ReconcileTest.choicesOfTheDesk());
      assertFalse(Files.exists(bundle()));
      assertFalse(Files.exists(root.resolve("reloaded")));
      return;
    }
    typesOfTheIdentity(".htm");
    var config= root.resolve("config").resolve("mimeapps.list");
    var etc= root.resolve("etc").resolve("mimeapps.list");
    var text= "[Default Applications]\napplication/x-fearless-htm=browser.desktop\n";
    Fs.writeUtf8(config, text);
    Fs.writeUtf8(etc, text);
    assertTrue(etc.toFile().setWritable(false));
    try{
      assertFalse(Files.isWritable(etc), "This test needs a user that the permission denies: run the tests as a normal user, not as root.");
      assertEquals("notTaken {.htm="+etc+"}", refusedTaking(List.of(".htm"), ".htm"));
    }
    finally{ etc.toFile().setWritable(true); }
    assertEquals(text, Fs.readUtf8(config));
    assertEquals(List.of(), ran);
  }
  @Test void aFearlessExtensionAnotherProgramHoldsIsNotOurs(){
    if (Fs.isWindows()){
      importReg(regKey(classes+".ffile942", "", "otherProgram.ffile942")+regKey(classes+".ffile901\\OpenWithProgids", "otherProgram.ffile901", ""));
      assertEquals("notOurs {.ffile942=otherProgram}", refused(".ffile901", ".ffile942"));
      assertEquals(List.of(), FileAssociations.identities(family));
      assertFalse(exists(classes+identity+".ffile901"));
      reconcile(".ffile901");
      assertEquals(Map.of("otherProgram.ffile901", "", identity+".ffile901", ""), values(classes+".ffile901\\OpenWithProgids"));
      return;
    }
    if (Fs.isMac()){
      types.put("ffile042", List.of(sketch));
      holders.put(".ffile042", sketch.bundle());
      assertEquals("notOurs {.ffile042=Sketch}", refused(".ffile042"));
      assertFalse(Files.exists(bundle()));
      return;
    }
    sysMime("globs2", "50:application/x-other:*.ffile042\n60:application/x-wide:*.ffile04[0-9]\n70:application/x-near:*.ffile043\n");
    Fs.writeUtf8(sys.resolve("applications").resolve("other.desktop"), "[Desktop Entry]\nMimeType=application/x-other;application/x-near;\n");
    Fs.writeUtf8(sys.resolve("applications").resolve("vim.desktop"), "[Desktop Entry]\nMimeType=application/x-wide;application/x-fearless-ffile052;\n");
    assertEquals("notOurs {.ffile042=vim}", refused(".htm", ".ffile042"));
    assertFalse(Files.exists(home));
    reconcile(".ffile052", ".fapp001");
    assertEquals("MimeType=application/x-fearless-ffile052;application/x-fearless-fapp001;", mimeTypes());
  }
  @Test void theExtensionFearlessKeepsTheTypeOfTheFamily() throws Exception{
    if (Fs.isWindows()){
      try (var _= aside(classes+".fearless"); var _= aside(fileExts+".fearless")){
        reconcile(".fearless");
        assertEquals(Optional.of(identity+".fearless"), value(classes+".fearless", ""));
        FileAssociations.eradicateAll(family, IllegalStateException::new);
        importReg(regKey(classes+".fearless", "", "otherProgram.fearless"));
        assertEquals("notOurs {.fearless=otherProgram}", refused(".fearless"));
      }
      return;
    }
    if (Fs.isMac()){
      reconcile(".fearless");
      plistIs(document("fearless", "Owner", "fearlessmanaged0-001.fearless"), exported("fearless"));
      assertEquals(bundleFiles(icns("fearless")), files());
      assertEquals(List.of(bundle()), registered);
      holders.put(".fearless", sketch.bundle());
      assertEquals("notOurs {.fearless=Sketch}", refused(".fearless"));
      return;
    }
    sysMime("globs2", "50:application/x-other:*.fearless\n");
    reconcile(".fearless");
    Err.strCmp(mimeInfo("\"><glob pattern=\"*.fearless\" weight=\"100\"/><sub-class-of type=\"application/x-other\"/>"), Fs.readUtf8(packageFile()));
    assertEquals("MimeType=application/x-fearless;", mimeTypes());
    Fs.writeUtf8(sys.resolve("applications").resolve("vim.desktop"), "[Desktop Entry]\nMimeType=application/x-other;\n");
    assertEquals("notOurs {.fearless=vim}", refused(".fearless"));
  }
  @Test void releasingAnExtensionLeavesTheIdentityWithoutIt(){
    if (Fs.isWindows()){
      reconcile(".ffile901", ".fassochtm", ".ffile942");
      reconcile(".ffile901", ".ffile942");
      assertEquals(Map.of(".ffile901", identity+".ffile901", ".ffile942", identity+".ffile942"), values(user+identity+"\\Capabilities\\FileAssociations"));
      assertFalse(exists(classes+identity+".fassochtm"));
      assertTrue(exists(classes+identity+".ffile901"));
      assertTrue(exists(classes+identity+".ffile942"));
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123", ".ffile042");
      reconcile(".fapp123");
      plistIs(document("fapp123", "Owner", "fearlessmanaged0-001.fapp123"), exported("fapp123"));
      assertEquals(bundleFiles(icns("fapp123")), files());
      return;
    }
    reconcile(".fearless", ".htm", ".ffile042");
    ran.clear();
    reconcile(".fearless", ".ffile042");
    Err.strCmp(mimeInfo(
      "\"><glob pattern=\"*.fearless\" weight=\"100\"/>",
      "-ffile042\"><glob pattern=\"*.ffile042\" weight=\"100\"/>"), Fs.readUtf8(packageFile()));
    assertEquals("MimeType=application/x-fearless;application/x-fearless-ffile042;", mimeTypes());
    assertEquals(2, icons().size());
    assertEquals(rebuilt(), ran);
  }
  @Test void anExtensionMatchesTheTypesOfTheSystemInTheLetterCaseTheSystemSays(){
    if (Fs.isWindows()){
      importReg(regKey(classes+".FASSOCHTM\\OpenWithProgids", "otherProgram.fassochtm", ""));
      reconcile(".fassochtm");
      assertEquals(Optional.of(identity+".fassochtm"), value(classes+".FASSOCHTM", ""));
      assertEquals(Map.of("otherProgram.fassochtm", "", identity+".fassochtm", ""), values(classes+".fassochtm\\OpenWithProgids"));
      return;
    }
    if (Fs.isMac()){
      MacAssociations.declared = declared;
      assertEquals(declared.apply("htm"), declared.apply("HTM"));
      reconcile(".htm");
      plistIs(document("htm", "Alternate", declared.apply("htm").getFirst().type()), "");
      return;
    }
    reconcile(".bar", ".c");
    Err.strCmp(mimeInfo(
      "-bar\"><glob pattern=\"*.bar\" weight=\"100\"/><sub-class-of type=\"text/x-bar\"/>",
      "-c\"><glob pattern=\"*.c\" weight=\"100\"/><sub-class-of type=\"text/x-csrc\"/>"), Fs.readUtf8(packageFile()));
  }
  @Test void theTypesTheFamilyDeclaredAreNotTypesOfOtherPrograms(){
    if (Fs.isWindows()){
      var old= older+".ffile901";
      importReg(regKey(classes+old+"\\shell\\open\\command", "", "\"C:\\Program Files\\"+older+".exe\" \"%1\"")
        +regKey(classes+".ffile901", "", old)
        +regKey(classes+".ffile901\\OpenWithProgids", old, ""));
      reconcile(".ffile901");
      assertFalse(exists(classes+old));
      assertEquals(Optional.of(identity+".ffile901"), value(classes+".ffile901", ""));
      assertEquals(Map.of(identity+".ffile901", ""), values(classes+".ffile901\\OpenWithProgids"));
      return;
    }
    if (Fs.isMac()){
      types.put("fapp123", List.of(new Declared("fearlessmanaged0-001.fapp123", bundle()), sketch));
      types.put("ffile123", List.of(new Declared("fearlessmanaged0-001.ffile123", bundle())));
      reconcile(".ffile123");
      plistIs(document("ffile123", "Owner", "fearlessmanaged0-001.ffile123"), exported("ffile123"));
      holders.put(".fapp123", Path.of("/Applications/fearlessManaged0_000.app"));
      reconcile(".fapp123");
      plistIs(document("fapp123", "Alternate", "com.example.sketch"), "");
      assertEquals(choices("com.example.sketch"), ReconcileTest.choicesOfTheDesk());
      return;
    }
    var old= "fearlessManaged0_000";
    Fs.writeUtf8(home.resolve("mime").resolve("globs2"), "100:application/x-fearless-ffile001:*.ffile001\n");
    Fs.writeUtf8(home.resolve("mime").resolve("packages").resolve(old+".xml"),
      "  <mime-type type=\"application/x-fearless-ffile001\"><comment>x</comment><glob pattern=\"*.ffile001\" weight=\"100\"/><icon name=\""+old+"-1\"/></mime-type>\n");
    Fs.writeUtf8(home.resolve("applications").resolve(old+".desktop"), "[Desktop Entry]\nMimeType=application/x-fearless-ffile001;\n");
    Fs.writeUtf8(mimetypes().resolve(old+"-1.png"), "");
    reconcile(".ffile001");
    assertEquals("MimeType=application/x-fearless-ffile001;", mimeTypes());
    assertFalse(Files.exists(home.resolve("mime").resolve("packages").resolve(old+".xml")));
    assertFalse(Files.exists(mimetypes().resolve(old+"-1.png")));
  }
  @Test void anExtensionWithATypeOfAnotherProgramIsOpenedBelowThatType(){
    if (Fs.isWindows()){
      importReg(regKey(classes+".fassocqux", "", "otherProgram.fassocqux")+regKey(classes+".fassocqux\\OpenWithProgids", "otherProgram.fassocqux", ""));
      taking(List.of(".fassocqux"), ".fassocqux");
      assertEquals(Optional.of(identity+".fassocqux"), value(classes+".fassocqux", ""));
      assertEquals(Map.of("otherProgram.fassocqux", "", identity+".fassocqux", ""), values(classes+".fassocqux\\OpenWithProgids"));
      return;
    }
    if (Fs.isMac()){
      types.put("sketch", List.of(sketch, html));
      reconcile(".sketch");
      plistIs(document("sketch", "Alternate", "com.example.sketch"), "");
      assertFalse(Files.exists(preferencesFile()));
      holders.put(".sketch", sketch.bundle());
      taking(List.of(".sketch"), ".sketch", ".fapp123");
      assertEquals(choices("com.example.sketch"), ReconcileTest.choicesOfTheDesk());
      return;
    }
    Fs.writeUtf8(home.resolve("mime").resolve("globs2"), "100:application/x-gone:*.ffile001\n50:text/x-qux:*.qux\n");
    Fs.writeUtf8(home.resolve("mime").resolve("packages").resolve("other.xml"), "<mime-type type='text/x-qux'><glob pattern='*.qux'/></mime-type>\n");
    reconcile(".ffile001", ".qux");
    Err.strCmp(mimeInfo(
      "-ffile001\"><glob pattern=\"*.ffile001\" weight=\"100\"/>",
      "-qux\"><glob pattern=\"*.qux\" weight=\"100\"/><sub-class-of type=\"text/x-qux\"/>"), Fs.readUtf8(packageFile()));
  }
  @Test void anUnchangedSetWritesNothingAndRefreshesTheDesktopAgain(){
    if (Fs.isWindows()){
      reconcile(".ffile901", ".fassochtm");
      importReg(regKey(user+identity, "kept", "by the test"));
      ran.clear();
      reconcile(".ffile901", ".fassochtm");
      assertEquals(Optional.of("by the test"), value(user+identity, "kept"));
      assertEquals(rebuilt(), ran);
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      var written= Fs.of(() -> Files.getLastModifiedTime(contents("Info.plist")));
      reconcile(".fapp123");
      assertEquals(written, Fs.of(() -> Files.getLastModifiedTime(contents("Info.plist"))));
      assertEquals(List.of(bundle(), bundle()), registered);
      return;
    }
    reconcile(".fearless", ".htm");
    Fs.writeUtf8(home.resolve("mime").resolve("globs2"), "100:application/x-fearless:*.fearless\n100:application/x-fearless-htm:*.htm\n");
    Fs.writeUtf8(home.resolve("mime").resolve("subclasses"), "application/x-fearless-htm text/html\napplication/x-fearless-htm application/xhtml+xml\n");
    Fs.ofV(() -> Files.setLastModifiedTime(packageFile(), FileTime.fromMillis(1000)));
    ran.clear();
    reconcile(".fearless", ".htm");
    assertEquals(1000, Fs.lastModified(packageFile()));
    assertEquals(rebuilt(), ran);
  }
  @Test void aChangeTheDeskRefusesIsReported(){
    if (Fs.isWindows()){
      var key= user+identity;
      importReg(regKey(key, "kept", "by the test"));
      deny(key, "CreateSubKey,SetValue");
      try{ Err.strCmp("halfDone RegSetKeyValueW "+key+"\\Capabilities ApplicationName\n[###]", refused(".ffile901")); }
      finally{ permit(key, "CreateSubKey,SetValue"); }
      assertEquals(Map.of("kept", "by the test"), values(key));
      return;
    }
    if (Fs.isMac()){
      MacAssociations.register = _ -> -43;
      Err.strCmp("halfDone LSRegisterURL [###]/home/fearlessManaged0_001.app\n-43", refused(".fapp123"));
      return;
    }
    Fs.writeUtf8(mimetypes().resolve(identity+"-0123abc.png"), "");
    assertTrue(mimetypes().toFile().setWritable(false));
    try{
      assertFalse(Files.isWritable(mimetypes()), "This test needs a user that the permission denies: run the tests as a normal user, not as root.");
      assertEquals("notWritable "+mimetypes(), refused(".ffile001"));
    }
    finally{ mimetypes().toFile().setWritable(true); }
    assertTrue(Files.exists(mimetypes().resolve(identity+"-0123abc.png")));
    assertFalse(Files.exists(desktopFile()));
    assertEquals(List.of(), ran);
  }
  @Test void aRegistrationOfTheIdentityTheUserCanNotChangeIsRefusedBeforeWritingAnything() throws Exception{
    if (Fs.isWindows()){
      try (var _= allUsers(identity)){
        reconcile(".ffile901");
        assertEquals(List.of(identity), FileAssociations.identities(family));
        assertEquals(Optional.of(identity+".ffile901"), value(machine+identity+"\\Capabilities\\FileAssociations", ".ffile901"));
        assertTrue(exists(machine+"Classes\\"+identity+".ffile901"));
      }
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      withReadOnly(MacAssociations.home, () -> {
        assertEquals("notWritable "+MacAssociations.home, refused());
        assertEquals("notWritable "+MacAssociations.home, refused(".ffile002"));
      });
      plistIs(document("fapp123", "Owner", "fearlessmanaged0-001.fapp123"), exported("fapp123"));
      assertEquals(List.of(bundle()), registered);
      return;
    }
    reconcile(".ffile001");
    var apps= sys.resolve("applications");
    Fs.writeUtf8(apps.resolve(identity+".desktop"), "[Desktop Entry]\n");
    assertTrue(apps.toFile().setWritable(false));
    try{
      assertFalse(Files.isWritable(apps), "This test needs a user that the permission denies: run the tests as a normal user, not as root.");
      assertEquals("notWritable "+apps, refused(".ffile002"));
    }
    finally{ apps.toFile().setWritable(true); }
    assertTrue(Files.exists(desktopFile()));
  }
  @Test void anEntryOfAWindowClassTheUserCanNotChangeIsRefusedBeforeWritingAnything(){
    if (Fs.isWindows()){
      var unread= new WindowIcon("fearless-1a2b-game.IconsGame", "Game", Path.of("C:\\projects\\game"), root.resolve("nowhere").resolve("game.png"));
      reconcile(List.of(unread), ".ffile901");
      assertEquals(List.of(identity), FileAssociations.identities(family));
      return;
    }
    if (Fs.isMac()){
      var game= new WindowIcon("fearless-1a2b-game.IconsGame", "Game", Path.of("/projects/game"), icon(0x00ff00));
      reconcile(List.of(game), ".fapp123");
      withReadOnly(contents("Resources"), () -> assertEquals("notWritable "+contents("Resources"), assertThrows(IllegalStateException.class, () -> reconcile(List.of(game), ".ffile002")).getMessage()));
      plistIs(document("fapp123", "Owner", "fearlessmanaged0-001.fapp123"), exported("fapp123"));
      assertEquals(List.of(bundle()), registered);
      return;
    }
    reconcile(".ffile001");
    var apps= sys.resolve("applications");
    Fs.writeUtf8(apps.resolve(identity+"-1a2b.desktop"), "[Desktop Entry]\nNoDisplay=true\n");
    assertTrue(apps.toFile().setWritable(false));
    try{
      assertFalse(Files.isWritable(apps), "This test needs a user that the permission denies: run the tests as a normal user, not as root.");
      assertEquals("notWritable "+apps, refused(".ffile002"));
    }
    finally{ apps.toFile().setWritable(true); }
    assertTrue(Files.exists(desktopFile()));
  }
  @Test void aWindowOfAProgramShowsTheIconOfItsProject(){
    if (Fs.isWindows()){
      var game= new WindowIcon("fearless-1a2b-game.IconsGame", "Game", Path.of("C:\\projects\\game"), icon(0x00ff00));
      reconcile(List.of(game), ".ffile901");
      var written= reg("query", user+identity, "/s").orElseThrow()+reg("query", classes+identity+".ffile901", "/s").orElseThrow();
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      reconcile(".ffile901");
      assertEquals(written, reg("query", user+identity, "/s").orElseThrow()+reg("query", classes+identity+".ffile901", "/s").orElseThrow());
      return;
    }
    var game= new WindowIcon("fearless-1a2b-game.IconsGame", "Game", Path.of("/projects/game"), icon(0x00ff00));
    var tool= new WindowIcon("fearless-1a2b-game.IconsTool", "Game", Path.of("/projects/game"), icon(0x00ff00));
    if (Fs.isMac()){
      reconcile(List.of(game, tool), ".fearless");
      plistIs(document("fearless", "Owner", "fearlessmanaged0-001.fearless"), exported("fearless"));
      assertEquals(bundleFiles(icns("fearless")), files());
      assertEquals(List.of(identity), FileAssociations.identities(family));
      return;
    }
    reconcile(List.of(game, tool), ".fearless");
    var entries= windowEntries();
    assertEquals(2, entries.size());
    entries.forEach(n -> assertTrue(n.matches(identity+"-[0-9a-f]+\\.desktop"), n));
    Err.strCmp("""
[Desktop Entry]
Type=Application
Name=Game
Exec=env LC_ALL=C.UTF-8 "/opt/fearlessManaged0_001/bin/fearlessManaged0_001" "/projects/game"
Icon=[###]/home/icons/hicolor/256x256/mimetypes/fearlessManaged0_001-[###].png
StartupWMClass=fearless-1a2b-game.IconsGame
NoDisplay=true
Terminal=false
""", Fs.readUtf8(home.resolve("applications").resolve(entries.stream().filter(n -> Fs.readUtf8(home.resolve("applications").resolve(n)).contains("IconsGame")).findFirst().orElseThrow())));
    assertEquals(2, icons().size());
    assertEquals(List.of(identity), FileAssociations.identities(family));
    ran.clear();
    reconcile(List.of(game, tool), ".fearless");
    assertEquals(rebuilt(), ran);
    reconcile(List.of(game), ".fearless");
    assertEquals(1, windowEntries().size());
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of(), windowEntries());
  }
  @Test void aRegistrationOfAnotherProgramThatCanNotBeReadIsIgnored(){
    if (Fs.isWindows()){
      importReg("\r\n["+classes+".ffile901]\r\n\"half\uD800\"=\"x\"\r\n\"lines\"=hex(1):61,00,0a,00,62,00,00,00\r\n"
        +"\r\n["+classes+".ffile901\\OpenWithProgids]\r\n\"half\uD800.ffile901\"=\"\"\r\n\"otherProgram.ffile901\"=\"\"\r\n");
      reconcile(".ffile901");
      assertEquals(Optional.of(identity+".ffile901"), value(classes+".ffile901", ""));
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertNotEquals(Optional.of(identity+".ffile901"), value(classes+".ffile901", ""));
      assertEquals(Optional.of("a"), value(classes+".ffile901", "lines"));
      assertEquals(2, values(classes+".ffile901\\OpenWithProgids").size());
      return;
    }
    if (Fs.isMac()){
      MacAssociations.declared = declared;
      var unreadable= Fs.of(root::toRealPath).resolve("other.app");
      var plist= unreadable.resolve("Contents").resolve("Info.plist");
      Fs.writeUtf8(plist, MacAssociations.plist("otherProgram", "Other", "", unreadableExported).replace("</dict></plist>", "<key>broken</dict></plist>"));
      assertEquals(0, register.applyAsInt(unreadable));
      try{
        assertEquals(List.of(), declared.apply("ffile996"));
        reconcile(".ffile996");
        assertEquals(List.of(identity), FileAssociations.identities(family));
      }
      finally{
        Fs.writeUtf8(plist, MacAssociations.plist("otherProgram", "Other", "", ""));
        assertEquals(0, register.applyAsInt(unreadable));
      }
      return;
    }
    var other= sys.resolve("applications").resolve("other.desktop");
    Fs.ensureDir(other.getParent());
    Fs.ofV(() -> Fs.write(other, "[Desktop Entry]\nName=Caf\u00E9\nMimeType=application/x-fearless-ffile001;\n".getBytes(StandardCharsets.ISO_8859_1)));
    reconcile(".ffile001");
    assertTrue(Files.exists(desktopFile()));
  }
  @Test void removingEveryIdentityRemovesWhatIdentitiesAlreadyGoneLeft(){
    if (Fs.isWindows()){
      var gone= older+".ffile901";
      importReg(regKey(classes+gone+"\\shell\\open\\command", "", "\"C:\\Program Files\\"+older+".exe\" \"%1\"")
        +regKey(classes+".ffile901", "", gone)
        +regKey(classes+".ffile901\\OpenWithProgids", gone, "")
        +regKey(classes+".ffile901\\OpenWithProgids", "otherProgram.ffile901", "")
        +regKey(classes+"otherProgram.ffile901\\shell\\open\\command", "", "\"C:\\Program Files\\other.exe\" \"%1\""));
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertFalse(exists(classes+gone));
      assertNotEquals(Optional.of(gone), value(classes+".ffile901", ""));
      assertEquals(Map.of("otherProgram.ffile901", ""), values(classes+".ffile901\\OpenWithProgids"));
      assertTrue(exists(classes+"otherProgram.ffile901\\shell\\open\\command"));
      assertEquals(rebuilt(), ran);
      return;
    }
    if (Fs.isMac()){
      var gone= MacAssociations.home.resolve("fearlessBin0_001.app");
      Fs.writeUtf8(gone.resolve("Contents").resolve("MacOS").resolve("fearlessBin0_001"), "");
      Fs.writeUtf8(MacAssociations.home.resolve("other.app").resolve("Contents").resolve("Info.plist"), "");
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertEquals(List.of(MacAssociations.home.resolve("other.app")), Fs.of(() -> { try (var s= Files.list(MacAssociations.home)){ return s.toList(); }}));
      assertEquals(List.of(gone), registered);
      return;
    }
    Fs.writeUtf8(mimetypes().resolve("fearlessBin0_001-a52baa.png"), "");
    Fs.writeUtf8(mimetypes().resolve("fearlessBin0_001.png"), "");
    Fs.writeUtf8(mimetypes().resolve("other-a52baa.png"), "");
    Fs.writeUtf8(appIcon().resolveSibling("fearlessBin0_001.png"), "");
    Fs.writeUtf8(appIcon().resolveSibling("other.png"), "");
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of("fearlessBin0_001.png", "other-a52baa.png"), icons());
    assertEquals(List.of(appIcon().resolveSibling("other.png")), Fs.of(() -> { try (var s= Files.list(appIcon().getParent())){ return s.toList(); }}));
    assertEquals(List.of(), ran);
  }
  @Test void eachReconcileWritesTheIconsOfItsExtensions(){
    if (Fs.isWindows()){
      var first= root.resolve("first.ico");
      var second= root.resolve("second.ico");
      reconcile(List.of(new Icon(".ffile901", first, icon(1))));
      assertEquals(Optional.of(first+",0"), value(classes+identity+".ffile901\\DefaultIcon", ""));
      reconcile(List.of(new Icon(".ffile901", second, icon(1))));
      assertEquals(Optional.of(second+",0"), value(classes+identity+".ffile901\\DefaultIcon", ""));
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      var icns= ByteBuffer.wrap(Fs.of(() -> Files.readAllBytes(contents("Resources/"+icns("fapp123")))));
      var image= new byte[icns.capacity() - 16];
      icns.get(16, image);
      assertEquals(List.of(0x69636e73, icns.capacity(), 0x69633038, image.length + 8), List.of(icns.getInt(0), icns.getInt(4), icns.getInt(8), icns.getInt(12)));
      assertEquals(256, Fs.of(() -> ImageIO.read(new java.io.ByteArrayInputStream(image))).getWidth());
      return;
    }
    reconcile(".ffile001", ".htm");
    var wanted= icons();
    Fs.writeUtf8(mimetypes().resolve(identity+"-0123abc.png"), "");
    Fs.writeUtf8(mimetypes().resolve(identity+"x-0123abc.png"), "");
    Fs.writeUtf8(mimetypes().resolve(identity+"-other-0123abc.png"), "");
    Fs.writeUtf8(mimetypes().resolve(identity+"-0123ABC.png"), "");
    ran.clear();
    reconcile(".ffile001", ".htm");
    assertEquals(rebuilt(), ran);
    var others= List.of(identity+"-0123ABC.png", identity+"-other-0123abc.png", identity+"x-0123abc.png");
    assertEquals(Stream.concat(wanted.stream(), others.stream()).sorted().toList(), icons());
    ran.clear();
    reconcile(".ffile001", ".htm");
    assertEquals(rebuilt(), ran);
    reconcile(".ffile001");
    assertEquals(1, icons().stream().filter(n -> n.matches(identity+"-[0-9a-f]+\\.png")).count());
  }
  @Test void removingTheIdentityRemovesEverythingItWrote(){
    if (Fs.isWindows()){
      importReg(regKey(classes+".fassochtm\\OpenWithProgids", "otherProgram.fassochtm", ""));
      reconcile(".ffile901", ".fassochtm");
      ran.clear();
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertEquals(rebuilt(), ran);
      assertFalse(exists(user+identity));
      assertEquals(Optional.empty(), value(registeredApplications, identity));
      assertFalse(exists(classes+identity+".ffile901"));
      assertFalse(exists(classes+identity+".fassochtm"));
      assertFalse(exists(classes+".ffile901"));
      assertEquals(Map.of("otherProgram.fassochtm", ""), values(classes+".fassochtm\\OpenWithProgids"));
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertFalse(Files.exists(bundle()));
      return;
    }
    reconcile(".ffile001", ".htm");
    Fs.writeUtf8(mimetypes().resolve(identity+"-0123abc.png"), "");
    Fs.writeUtf8(mimetypes().resolve("other-0123abc.png"), "");
    ran.clear();
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(rebuilt(), ran);
    assertEquals(List.of("other-0123abc.png"), icons());
    assertFalse(Files.exists(appIcon()));
    assertFalse(Files.exists(desktopFile()));
    assertFalse(Files.exists(packageFile()));
  }
  @Test void anIdentityTheSystemKeepsForAllUsersIsFoundAndReplaced() throws Exception{
    if (Fs.isWindows()){
      try (var _= allUsers(older)){
        assertEquals(List.of(), FileAssociations.identities(family));
        reconcile(".ffile901");
        assertEquals(List.of(), replaced);
        assertEquals(List.of(identity), FileAssociations.identities(family));
        assertTrue(exists(machine+"Classes\\"+older+".ffile901"));
      }
      return;
    }
    if (Fs.isMac()){
      var installed= root.resolve("Applications").resolve("fearlessManaged0_000.app").resolve("Contents").resolve("Info.plist");
      Fs.writeUtf8(installed, MacAssociations.plist("fearlessManaged0_000", "Fearless Manager", "", ""));
      assertEquals(List.of(), FileAssociations.identities(family));
      reconcile(".ffile001");
      assertEquals(List.of(identity), FileAssociations.identities(family));
      assertTrue(Files.exists(installed));
      return;
    }
    var old= "fearlessManaged0_000";
    Fs.writeUtf8(sys.resolve("applications").resolve(old+".desktop"), "[Desktop Entry]\nMimeType=application/x-fearless-ffile001;\n");
    Fs.writeUtf8(sys.resolve("mime").resolve("packages").resolve(old+".xml"), "<mime-type type=\"application/x-fearless-ffile001\"><glob pattern=\"*.ffile001\"/></mime-type>\n");
    assertEquals(List.of(old), FileAssociations.identities(family));
    reconcile(".ffile001");
    assertEquals(List.of(identity), FileAssociations.identities(family));
  }
  @Test void aFamilyRegistrationInAnotherLayoutDeclaresNoTypeOfAnotherProgram(){
    if (Fs.isWindows()){
      var old= older+".ffile901";
      importReg(regKey(user+older+"\\Capabilities\\FileAssociations", ".ffile901", old)
        +regKey(classes+old+"\\shell\\open\\command", "", "C:\\Program Files\\"+older+".exe \"%1\"")
        +regKey(classes+".ffile901", "", old)
        +regKey(classes+".ffile901\\OpenWithProgids", old, ""));
      reconcile(".ffile901");
      assertEquals(List.of(identity), FileAssociations.identities(family));
      return;
    }
    if (Fs.isMac()){
      MacAssociations.declared = declared;
      MacAssociations.register = register;
      var old= MacAssociations.home.resolve("fearlessManaged0_000.app");
      Fs.writeUtf8(old.resolve("Contents").resolve("Info.plist"), """
<?xml version="1.0" encoding="UTF-8"?>
<plist version="1.0">
<dict>
  <key>UTExportedTypeDeclarations</key>
  <array>
    <dict>
      <key>UTTypeTagSpecification</key>
      <dict><key>public.filename-extension</key><array><string>ffile997</string></array></dict>
      <key>UTTypeIdentifier</key>
      <string>fearlessmanaged0-000.ffile997</string>
      <key>UTTypeConformsTo</key>
      <array><string>public.data</string></array>
    </dict>
  </array>
  <key>CFBundlePackageType</key>
  <string>APPL</string>
  <key>CFBundleIdentifier</key>
  <string>fearlessManaged0-000</string>
</dict>
</plist>
""");
      assertEquals(0, register.applyAsInt(old));
      assertEquals(List.of(new Declared("fearlessmanaged0-000.ffile997", old)), declared.apply("ffile997"));
      reconcile(".ffile997");
      assertEquals(List.of(identity), FileAssociations.identities(family));
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      assertEquals(List.of(), declared.apply("ffile997"));
      return;
    }
    var old= "fearlessManaged0_000";
    sysMime("globs2", "100:application/x-fearless-ffile001:*.ffile001\n");
    Fs.writeUtf8(sys.resolve("mime").resolve("packages").resolve(old+".xml"), """
<?xml version="1.0" encoding="UTF-8"?>
<mime-info xmlns="http://www.freedesktop.org/standards/shared-mime-info">
  <mime-type type="application/x-fearless-ffile001">
    <glob pattern="*.ffile001" weight="100"/>
  </mime-type>
</mime-info>
""");
    reconcile(".ffile001");
    assertEquals(List.of(identity), FileAssociations.identities(family));
  }
  @Test void aReconcileRefreshesOnlyWhatItChanges(){
    if (Fs.isWindows()){
      reconcile(".ffile901", ".fassochtm", ".ffile942");
      assertEquals(rebuilt(), ran);
      FileAssociations.eradicateAll(family, IllegalStateException::new);
      ran.clear();
      reconcile();
      assertEquals(List.of(), ran);
      return;
    }
    if (Fs.isMac()){
      reconcile(".fapp123");
      assertEquals(List.of(bundle()), registered);
      return;
    }
    Fs.writeUtf8(sys.resolve("applications").resolve("browser.desktop"), "[Desktop Entry]\nMimeType=text/html;\n");
    taking(List.of(".htm"), ".htm");
    assertEquals(rebuilt(), ran);
  }
  @Test void noExtensionLeavesNothingOfTheIdentity(){
    if (Fs.isWindows()){
      reconcile(".ffile901");
      reconcile();
      assertFalse(exists(user+identity));
      assertEquals(Optional.empty(), value(registeredApplications, identity));
      assertFalse(exists(classes+identity+".ffile901"));
      ran.clear();
      reconcile();
      assertEquals(List.of(), ran);
      return;
    }
    if (Fs.isMac()){
      reconcile(".fearless");
      reconcile();
      assertFalse(Files.exists(bundle()));
      assertEquals(List.of(bundle(), bundle()), registered);
      return;
    }
    reconcile(".ffile001");
    reconcile();
    assertEquals(List.of(), icons());
    assertFalse(Files.exists(appIcon()));
    assertFalse(Files.exists(desktopFile()));
    ran.clear();
    reconcile();
    assertEquals(List.of(), ran);
  }
  @Test void extensionsWithTheSameImageShareOneIconFile(){
    var png= icon(0x0000ff);
    reconcile(List.of(new Icon(".ffile901", png, png), new Icon(".ffile942", png, png)));
    if (Fs.isMac()){
      assertEquals(5, files().size(), files().toString());
      Err.strCmp("[###]<key>CFBundleDocumentTypes</key><array>\n<dict>[###]<key>LSItemContentTypes</key><array><string>fearlessmanaged0-001.ffile901</string><string>fearlessmanaged0-001.ffile942</string></array></dict>\n</array>[###]", Fs.readUtf8(contents("Info.plist")));
      return;
    }
    if (Fs.isLinux()){ assertEquals(1, icons().size()); }
  }
  @Test void reconcileAndEradicateAllHoldTheLockOfTheFamilyFromStartToEnd(){
    Fs.ensureDir(FileAssociations.lockFolder);
    try (var ch= FileChannel.open(FileAssociations.lockFolder.resolve("fearlessAssociations.lock"), StandardOpenOption.CREATE, StandardOpenOption.WRITE)){
      ch.lock();
      assertThrows(OverlappingFileLockException.class, () -> reconcile(".ffile901"));
      assertThrows(OverlappingFileLockException.class, () -> FileAssociations.eradicateAll(family, IllegalStateException::new));
    }
    catch (IOException e){ throw new UncheckedIOException(e); }
    assertEquals(List.of(), FileAssociations.identities(family));
    reconcile(".ffile901");
    assertEquals(List.of(identity), FileAssociations.identities(family));
  }
}
