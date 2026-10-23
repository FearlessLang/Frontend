package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.lang.ProcessBuilder.Redirect;
import java.util.List;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import fileAssociations.FileAssociations;
import tools.Fs;
import utils.Push;

/// FileAssociations on Windows, against keys of the registry of the current user that only this test uses.
final class WindowsAssociationsTest{
  private static final String identity= "fearlessCommonsTestProbe";
  private static final String ext= ".fcommonsprobe";
  private static final String progId= identity+ext;
  private static final String otherProgId= "anotherProgram"+ext;
  private static final String software= "HKCU\\Software\\";
  private static final String classes= software+"Classes\\";
  private static final String registered= software+"RegisteredApplications";
  @BeforeEach void windowsOnly(){ assumeTrue(Fs.isWindows()); cleanUp(); }
  @AfterEach void cleanUp(){
    if (!Fs.isWindows()){ return; }
    reg("delete", software+identity, "/f");
    reg("delete", registered, "/v", identity, "/f");
    reg("delete", classes+progId, "/f");
    reg("delete", classes+ext, "/f");
  }
  @Test void aCapabilitiesKeyIsAnIdentityAlsoWithoutARegisteredApplicationsValue(){
    assertEquals(0, reg("add", software+identity+"\\Capabilities", "/v", "ApplicationName", "/d", identity, "/f"));
    assertEquals(List.of(identity), FileAssociations.identities(identity::equals));
  }
  @Test void removingAnIdentityKeepsTheExtensionKeyWhileAnotherProgramStillClaimsIt(){
    assertEquals(0, reg("add", registered, "/v", identity, "/d", "Software\\"+identity+"\\Capabilities", "/f"));
    assertEquals(0, reg("add", software+identity+"\\Capabilities\\FileAssociations", "/v", ext, "/d", progId, "/f"));
    assertEquals(0, reg("add", classes+progId, "/ve", "/d", identity, "/f"));
    assertEquals(0, reg("add", classes+ext, "/ve", "/d", progId, "/f"));
    assertEquals(0, reg("add", classes+ext+"\\OpenWithProgids", "/v", progId, "/d", "x", "/f"));
    assertEquals(0, reg("add", classes+ext+"\\OpenWithProgids", "/v", otherProgId, "/d", "x", "/f"));
    assertEquals(List.of(identity), FileAssociations.identities(identity::equals));
    FileAssociations.eradicateAll(identity::equals, IllegalStateException::new);
    assertEquals(List.of(), FileAssociations.identities(identity::equals));
    assertEquals(1, reg("query", classes+progId));
    assertEquals(0, reg("query", classes+ext+"\\OpenWithProgids", "/v", otherProgId));
  }
  private static int reg(String... args){
    var p= Fs.of(new ProcessBuilder(Push.of("reg", List.of(args))).redirectErrorStream(true).redirectOutput(Redirect.DISCARD)::start);
    try{ return p.waitFor(); }
    catch (InterruptedException e){ throw new AssertionError(e); }
  }
}
