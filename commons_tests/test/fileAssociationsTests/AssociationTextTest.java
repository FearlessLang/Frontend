package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.Test;

import fileAssociations.Icon;
import fileAssociations.LinuxAssociations;
import fileAssociations.WindowsAssociations;
import utils.OneOr;

final class AssociationTextTest{
  private static final String linuxLauncher= "/home/me/fearlessManaged0_001/bin/fearlessManaged0_001";
  private static final Path winLauncher= Path.of("C:\\fearlessManaged0_001\\fearlessManaged0_001.exe");
  private static final Path proof= Path.of("C:\\fearlessManaged0_001\\proof.ico");
  private static final Path programIco= Path.of("C:\\fearlessManaged0_001\\app.ico");
  private static final String identity= "fearlessManaged0_001";
  @Test void theOneDesktopEntryHandsEveryKindToTheRunningLauncher(){
    var entry= LinuxAssociations.desktopEntry(identity, linuxLauncher, "controller-Main", List.of("application/x-fearless", "application/x-fproof"));
    assertTrue(entry.startsWith("[Desktop Entry]\n"), entry);
    assertTrue(entry.contains("Exec=env LC_ALL=C.UTF-8 \"/home/me/fearlessManaged0_001/bin/fearlessManaged0_001\" %f"), entry);
    assertTrue(entry.contains("MimeType=application/x-fearless;application/x-fproof;"), entry);
    assertTrue(entry.contains("Icon=fearlessManaged0_001"), entry);
    assertTrue(entry.contains("StartupWMClass=controller-Main"), entry);
  }
  private static String exec(String launcher){
    var entry= LinuxAssociations.desktopEntry(identity, launcher, "controller-Main", List.of("application/x-fearless"));
    return OneOr.of("one Exec line", entry.lines().filter(l -> l.startsWith("Exec=")));
  }
  @Test void theLauncherIsOneArgumentEvenWithSpaces(){
    assertEquals("Exec=env LC_ALL=C.UTF-8 \"/opt/my apps/fearless/bin/fearless\" %f", exec("/opt/my apps/fearless/bin/fearless"));
  }
  @Test void aPercentInTheLauncherIsNotAFieldCode(){
    assertEquals("Exec=env LC_ALL=C.UTF-8 \"/opt/100%%/fearless/bin/fearless\" %f", exec("/opt/100%/fearless/bin/fearless"));
  }
  @Test void aDollarInTheLauncherIsEscapedForBothTheQuoteAndTheString(){
    assertEquals("Exec=env LC_ALL=C.UTF-8 \"/opt/\\\\$apps/fearless/bin/fearless\" %f", exec("/opt/$apps/fearless/bin/fearless"));
  }
  @Test void theWindowClassIsTheMainClassTheWayTheToolkitNamesIt(){
    assertEquals("controller-Main", LinuxAssociations.windowClass("Controller/controller.Main"));
    assertEquals("mainCoordinator-Main", LinuxAssociations.windowClass("mainCoordinator.Main /some/project"));
  }
  @Test void thePictureNameFollowsWhatIsInsideItSoTheSameOneIsFiledOnce(){
    assertEquals(LinuxAssociations.hash(png(48)), LinuxAssociations.hash(png(48)));
    assertNotEquals(LinuxAssociations.hash(png(48)), LinuxAssociations.hash(png(32)));
  }
  @Test void theRegistryFileGivesEveryExtensionATypeOfItsOwn(){
    var lines= regFile();
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\Classes\\fearlessManaged0_001.fearless]"), lines.toString());
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\Classes\\fearlessManaged0_001.fproof]"), lines.toString());
    assertEquals("fearlessManaged0_001.fproof", WindowsAssociations.progId(identity, ".fproof"));
  }
  @Test void eachTypeCarriesItsOwnPictureAndTheOneSharedCommand(){
    var lines= regFile();
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\Classes\\fearlessManaged0_001.fproof\\DefaultIcon]"), lines.toString());
    assertTrue(lines.contains("@=\"C:\\\\fearlessManaged0_001\\\\proof.ico,0\""), lines.toString());
    assertEquals(2, lines.stream().filter(l -> l.endsWith("\\shell\\open\\command]")).count(), lines.toString());
    assertEquals(2, lines.stream().filter(l -> l.equals("@=\"\\\"C:\\\\fearlessManaged0_001\\\\fearlessManaged0_001.exe\\\" \\\"%1\\\"\"")).count(), lines.toString());
  }
  @Test void theRegistryFileCarriesTheApplicationsOwnPictureToo(){
    var lines= regFile();
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\fearlessManaged0_001\\Capabilities]"), lines.toString());
    assertTrue(lines.contains("\"ApplicationIcon\"=\"C:\\\\fearlessManaged0_001\\\\app.ico,0\""), lines.toString());
  }
  @Test void theRegistryFilePointsEachExtensionAtItsOwnType(){
    var lines= regFile();
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\Classes\\.fearless]"), lines.toString());
    assertTrue(lines.contains("@=\"fearlessManaged0_001.fearless\""), lines.toString());
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\Classes\\.fproof\\OpenWithProgids]"), lines.toString());
    assertTrue(lines.contains("\"fearlessManaged0_001.fproof\"=\"\""), lines.toString());
  }
  @Test void theRegistryFileSaysThisFearlessIsAnAppAndWhatItOpens(){
    var lines= regFile();
    assertTrue(lines.contains("\"ApplicationName\"=\"fearlessManaged0_001\""), lines.toString());
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\fearlessManaged0_001\\Capabilities\\FileAssociations]"), lines.toString());
    assertTrue(lines.contains("\".fproof\"=\"fearlessManaged0_001.fproof\""), lines.toString());
  }
  @Test void theRegistryFileListsThisFearlessAmongTheRegisteredApplications(){
    var lines= regFile();
    assertTrue(lines.contains("[HKEY_CURRENT_USER\\Software\\RegisteredApplications]"), lines.toString());
    assertTrue(lines.contains("\"fearlessManaged0_001\"=\"Software\\\\fearlessManaged0_001\\\\Capabilities\""), lines.toString());
  }
  @Test void theExtensionsWeHoldAreReadFromTheOneKeyThatFilesThem(){
    assertEquals("HKEY_CURRENT_USER\\Software\\fearlessManaged0_001\\Capabilities\\FileAssociations", WindowsAssociations.fileAssociations(identity));
    assertEquals(".fearless", WindowsAssociations.regName("    .fearless    REG_SZ    fearlessManaged0_001.fearless"));
  }
  @Test void theChoiceWindowsRemembersIsLookedForWhereWindowsKeepsIt(){
    assertEquals("HKCU\\Software\\Microsoft\\Windows\\CurrentVersion\\Explorer\\FileExts\\.fearless\\UserChoice", WindowsAssociations.userChoiceKey(".fearless"));
  }
  @Test void theRegistryFileUsesTheLineEndingsWindowsWrites(){
    var reg= WindowsAssociations.regFile(identity, winLauncher, winIcons(), programIco);
    assertEquals(reg.split("\r\n", -1).length, reg.split("\n", -1).length);
  }
  private static List<Icon> winIcons(){ return List.of(new Icon(".fearless", winLauncher, winLauncher), new Icon(".fproof", proof, proof)); }
  private static List<String> regFile(){ return WindowsAssociations.regFile(identity, winLauncher, winIcons(), programIco).lines().toList(); }
  private static byte[] png(int side){
    var res= new byte[24];
    write(res, 16, side);
    write(res, 20, side);
    return res;
  }
  private static void write(byte[] res, int at, int v){
    res[at] = (byte)(v>>>24); res[at+1] = (byte)(v>>>16); res[at+2] = (byte)(v>>>8); res[at+3] = (byte)v;
  }
}