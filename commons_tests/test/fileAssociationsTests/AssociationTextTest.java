package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fileAssociations.Icon;
import fileAssociations.LinuxAssociations;
import fileAssociations.WindowsAssociations;
import fileAssociations.WindowsAssociations.Entry;
import utils.OneOr;

final class AssociationTextTest{
  private static final String linuxLauncher= "/home/me/fearlessManaged0_001/bin/fearlessManaged0_001";
  private static final Path winLauncher= Path.of("C:\\fearlessManaged0_001\\fearlessManaged0_001.exe");
  private static final Path proof= Path.of("C:\\fearlessManaged0_001\\proof.ico");
  private static final String identity= "fearlessManaged0_001";
  private static final String name= "Fearless Manager";
  private static final String classes= "HKEY_CURRENT_USER\\Software\\Classes\\";
  @Test void theOneDesktopEntryHandsEveryKindToTheRunningLauncher(){
    assertEquals("""
[Desktop Entry]
Type=Application
Name=Fearless Manager
Exec=env LC_ALL=C.UTF-8 "/home/me/fearlessManaged0_001/bin/fearlessManaged0_001" %f
TryExec=/home/me/fearlessManaged0_001/bin/fearlessManaged0_001
Icon=fearlessManaged0_001
StartupWMClass=controller-Main
Terminal=false
MimeType=application/x-fearless;application/x-fproof;
""", LinuxAssociations.desktopEntry(identity, name, linuxLauncher, "controller-Main", List.of("application/x-fearless", "application/x-fproof")));
  }
  private static String exec(String launcher){
    var entry= LinuxAssociations.desktopEntry(identity, name, launcher, "controller-Main", List.of("application/x-fearless"));
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
  @Test void theRegistryGivesEveryExtensionATypeOfItsOwnWithItsPictureAndTheOneSharedCommandAndListsThisFearlessAsAnApp(){
    var capabilities= "HKEY_CURRENT_USER\\Software\\fearlessManaged0_001\\Capabilities";
    var opened= "\"C:\\fearlessManaged0_001\\fearlessManaged0_001.exe\" \"%1\"";
    assertEquals(List.of(
      new Entry(capabilities, "ApplicationName", "Fearless Manager"),
      new Entry(capabilities, "ApplicationIcon", "C:\\fearlessManaged0_001\\fearlessManaged0_001.exe,0"),
      new Entry(classes+"fearlessManaged0_001.fearless\\DefaultIcon", "", "C:\\fearlessManaged0_001\\fearlessManaged0_001.exe,0"),
      new Entry(classes+"fearlessManaged0_001.fearless\\shell\\open\\command", "", opened),
      new Entry(classes+".fearless", "", "fearlessManaged0_001.fearless"),
      new Entry(classes+".fearless\\OpenWithProgids", "fearlessManaged0_001.fearless", ""),
      new Entry(capabilities+"\\FileAssociations", ".fearless", "fearlessManaged0_001.fearless"),
      new Entry(classes+"fearlessManaged0_001.fproof\\DefaultIcon", "", "C:\\fearlessManaged0_001\\proof.ico,0"),
      new Entry(classes+"fearlessManaged0_001.fproof\\shell\\open\\command", "", opened),
      new Entry(classes+".fproof", "", "fearlessManaged0_001.fproof"),
      new Entry(classes+".fproof\\OpenWithProgids", "fearlessManaged0_001.fproof", ""),
      new Entry(capabilities+"\\FileAssociations", ".fproof", "fearlessManaged0_001.fproof"),
      new Entry("HKEY_CURRENT_USER\\Software\\RegisteredApplications", "fearlessManaged0_001", "Software\\fearlessManaged0_001\\Capabilities")), setup());
  }
  @Test void theChoiceWindowsRemembersIsLookedForWhereWindowsKeepsIt(){
    assertEquals("HKEY_CURRENT_USER\\Software\\Microsoft\\Windows\\CurrentVersion\\Explorer\\FileExts\\.fearless\\UserChoice", WindowsAssociations.userChoiceKey(".fearless"));
  }
  @Test void theRegistryKeepsTheDefaultOfAnExtensionTakenFromAnotherProgram(){
    var entries= WindowsAssociations.setup(identity, name, winLauncher, winIcons(), Map.of(".fproof", "SomeApp.fproof"));
    assertEquals(List.of(new Entry("HKEY_CURRENT_USER\\Software\\fearlessManaged0_001\\PreviousDefaults", ".fproof", "SomeApp.fproof")), entries.stream().filter(e -> !setup().contains(e)).toList());
    assertEquals(setup().size()+1, entries.size());
  }
  private static List<Icon> winIcons(){ return List.of(new Icon(".fearless", winLauncher, winLauncher), new Icon(".fproof", proof, proof)); }
  private static List<Entry> setup(){ return WindowsAssociations.setup(identity, name, winLauncher, winIcons(), Map.of()); }
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