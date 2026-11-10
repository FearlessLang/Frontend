package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.awt.image.BufferedImage;
import java.nio.ByteBuffer;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.ToIntFunction;
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
import fileAssociations.MacAssociations;
import fileAssociations.MacAssociations.Declared;
import tools.Fs;
import utils.Err;

/// FileAssociations.reconcile on macOS, against a folder of a test for the helper bundles and the types a test declares.
final class MacAssociationsTest{
  static{ Err.setUp(AssertionFailedError.class, Assertions::assertEquals, Assertions::assertTrue); }
  private static final Predicate<String> family= s -> s.contains("earless");
  private static final String identity= "fearlessManaged0_001";
  private static final Path command= Path.of("/Applications/it's here/fearlessManaged0_001.app/Contents/MacOS/fearlessManaged0_001");
  private static final Declared html= new Declared("public.html", Path.of("/System/Library/CoreServices/CoreTypes.bundle"));
  private static final Declared sketch= new Declared("com.example.sketch", Path.of("/Applications/Sketch.app"));
  @TempDir Path root;
  private final Path home= MacAssociations.home;
  private final Function<String,List<Declared>> declared= MacAssociations.declared;
  private final ToIntFunction<Path> register= MacAssociations.register;
  private final BiConsumer<Path,String> offer= MacAssociations.offer;
  private final Map<String,List<Declared>> types= new HashMap<>();
  private final List<Path> registered= new ArrayList<>();
  private final List<String> offered= new ArrayList<>();
  @BeforeEach void desktop(){
    assumeTrue(Fs.isMac());
    MacAssociations.home = Fs.of(root::toRealPath).resolve("home");
    MacAssociations.declared = e -> types.getOrDefault(e, List.of());
    MacAssociations.register = b -> { registered.add(b); return 0; };
    MacAssociations.offer = (_,type) -> offered.add(type);
  }
  @AfterEach void restore(){
    MacAssociations.home = home;
    MacAssociations.declared = declared;
    MacAssociations.register = register;
    MacAssociations.offer = offer;
  }
  private Path png(){
    var file= root.resolve("icon.png");
    Fs.ofV(() -> ImageIO.write(new BufferedImage(64, 64, BufferedImage.TYPE_INT_ARGB), "png", file.toFile()));
    return file;
  }
  private void reconcile(String... extensions){
    var icons= Stream.of(extensions).map(e -> new Icon(e, png(), png())).toList();
    FileAssociations.reconcile(identity, family, command, icons, List.of(), png(), _ -> {},
      s -> new IllegalStateException("ambiguous "+s),
      s -> new IllegalStateException("chosenByHand "+s),
      s -> new IllegalStateException("notOurs "+s),
      s -> new IllegalStateException("notWritable "+s),
      s -> new IllegalStateException("halfDone "+s));
  }
  private Path bundle(){ return MacAssociations.home.resolve(identity+".app"); }
  private Path contents(String file){ return bundle().resolve("Contents").resolve(file); }
  private List<String> files(){ return Fs.walk(bundle(), s -> s.filter(Files::isRegularFile).map(f -> bundle().relativize(f).toString()).sorted().toList()); }
  private static String document(String ext, String rank, String type){
    return "<dict><key>CFBundleTypeName</key><string>fearlessManaged0_001</string><key>CFBundleTypeRole</key><string>Viewer</string>"
      +"<key>CFBundleTypeIconFile</key><string>"+ext+".icns</string><key>LSHandlerRank</key><string>"+rank+"</string>"
      +"<key>LSItemContentTypes</key><array><string>"+type+"</string></array></dict>\n";
  }
  private static String exported(String ext){
    return "<dict><key>UTTypeIdentifier</key><string>fearlessmanaged0-001."+ext+"</string><key>UTTypeDescription</key><string>fearlessManaged0_001</string>"
      +"<key>UTTypeIconFile</key><string>"+ext+".icns</string><key>UTTypeConformsTo</key><array><string>public.data</string></array>"
      +"<key>UTTypeTagSpecification</key><dict><key>public.filename-extension</key><array><string>"+ext+"</string></array></dict></dict>\n";
  }
  private void plistIs(String documents, String exported){ assertEquals(MacAssociations.plist(identity, documents, exported), Fs.readUtf8(contents("Info.plist"))); }
  @Test void anExtensionNoBundleDeclaresGetsATypeOfTheIdentityWithTheRankOwner(){
    reconcile(".fapp123");
    Err.strCmp("""
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
<key>CFBundleExecutable</key><string>fearlessManaged0_001</string>
<key>CFBundleIdentifier</key><string>fearlessManaged0-001</string>
<key>CFBundleName</key><string>fearlessManaged0_001</string>
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
    assertEquals(List.of("Contents/Info.plist", "Contents/MacOS/fearlessManaged0_001", "Contents/Resources/_program.icns", "Contents/Resources/fapp123.icns"), files());
    assertEquals(List.of(bundle()), registered);
    assertEquals(List.of(), offered);
  }
  @Test void theLauncherOfTheHelperBundleRunsTheCommandWithFearlessCommandOpened(){
    reconcile(".fapp123");
    assertEquals("#!/bin/sh\nexec '/Applications/it'\\''s here/fearlessManaged0_001.app/Contents/MacOS/fearlessManaged0_001' FearlessCommandOpened\n", Fs.readUtf8(contents("MacOS/"+identity)));
    assertEquals(true, Files.isExecutable(contents("MacOS/"+identity)));
  }
  @Test void anIconIsAnIcnsHoldingOnePngOf256Pixels(){
    reconcile(".fapp123");
    var icns= ByteBuffer.wrap(Fs.of(() -> Files.readAllBytes(contents("Resources/fapp123.icns"))));
    var image= new byte[icns.capacity() - 16];
    icns.get(16, image);
    assertEquals(List.of(0x69636e73, icns.capacity(), 0x69633038, image.length + 8), List.of(icns.getInt(0), icns.getInt(4), icns.getInt(8), icns.getInt(12)));
    assertEquals(256, Fs.of(() -> ImageIO.read(new java.io.ByteArrayInputStream(image))).getWidth());
  }
  @Test void anExtensionMacOSDeclaresIsOpenedWithTheRankAlternateAndNotOffered(){
    types.put("htm", List.of(html));
    reconcile(".htm", ".fapp123");
    plistIs(document("htm", "Alternate", "public.html")+document("fapp123", "Owner", "fearlessmanaged0-001.fapp123"), exported("fapp123"));
    assertEquals(List.of(), offered);
  }
  @Test void anExtensionAnotherBundleDeclaresIsOfferedWhenFirstOpened(){
    types.put("sketch", List.of(sketch, html));
    reconcile(".sketch");
    plistIs(document("sketch", "Alternate", "com.example.sketch"), "");
    assertEquals(List.of("com.example.sketch"), offered);
    reconcile(".sketch", ".fapp123");
    reconcile(".sketch");
    assertEquals(List.of("com.example.sketch"), offered);
  }
  @Test void aTypeOfAHelperBundleIsNotADeclaredType(){
    types.put("fapp123", List.of(new Declared("fearlessmanaged0-001.fapp123", bundle()), sketch));
    types.put("ffile123", List.of(new Declared("fearlessmanaged0-001.ffile123", bundle())));
    reconcile(".ffile123");
    plistIs(document("ffile123", "Owner", "fearlessmanaged0-001.ffile123"), exported("ffile123"));
    assertEquals("notOurs {.fapp123=[Sketch]}", Assertions.assertThrows(IllegalStateException.class, () -> reconcile(".fapp123")).getMessage());
  }
  @Test void theBundleOfTheCommandDeclaresFearlessSoTheHelperBundleDeclaresNoTypeForFearless(){
    reconcile(".fearless");
    plistIs("", "");
    assertEquals(List.of("Contents/Info.plist", "Contents/MacOS/fearlessManaged0_001", "Contents/Resources/_program.icns"), files());
    assertEquals(List.of(bundle()), registered);
  }
  @Test void noExtensionRemovesTheHelperBundle(){
    reconcile(".fearless");
    reconcile();
    assertFalse(Files.exists(bundle()));
    assertEquals(List.of(bundle(), bundle()), registered);
  }
  @Test void anUnchangedSetWritesNothingAndRegistersAgain(){
    reconcile(".fapp123");
    var written= Fs.of(() -> Files.getLastModifiedTime(contents("Info.plist")));
    reconcile(".fapp123");
    assertEquals(written, Fs.of(() -> Files.getLastModifiedTime(contents("Info.plist"))));
    assertEquals(List.of(bundle(), bundle()), registered);
  }
  @Test void aFailedRegistrationIsReportedWithItsCode(){
    MacAssociations.register = _ -> -43;
    Err.strCmp("halfDone LSRegisterURL [###]/home/fearlessManaged0_001.app\n-43", Assertions.assertThrows(IllegalStateException.class, () -> reconcile(".fapp123")).getMessage());
  }
  @Test void theDesktopListsTheTypeOfARegisteredHelperBundleUntilTheIdentityIsRemoved(){
    MacAssociations.declared = declared;
    MacAssociations.register = register;
    assertEquals(html, declared.apply("htm").getFirst());
    reconcile(".fcommonsprobe");
    assertEquals(List.of(new Declared("fearlessmanaged0-001.fcommonsprobe", bundle())), declared.apply("fcommonsprobe"));
    FileAssociations.eradicateAll(family, IllegalStateException::new);
    assertEquals(List.of(), declared.apply("fcommonsprobe"));
    assertFalse(Files.exists(bundle()));
  }
}
