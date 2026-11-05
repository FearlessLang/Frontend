package fileAssociationsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.lang.ProcessBuilder.Redirect;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

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
  @TempDir Path tmp;
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
  private List<Path> replacedFrom(String openCommand){
    var file= tmp.resolve("probe.reg");
    var value= openCommand.replace("\\", "\\\\").replace("\"", "\\\"");
    var content= "Windows Registry Editor Version 5.00\r\n\r\n"
      +"[HKEY_CURRENT_USER\\Software\\"+identity+"\\Capabilities\\FileAssociations]\r\n\""+ext+"\"=\""+progId+"\"\r\n\r\n"
      +"[HKEY_CURRENT_USER\\Software\\Classes\\"+progId+"\\shell\\open\\command]\r\n@=\""+value+"\"\r\n";
    Fs.ofV(() -> Files.write(file, ("\uFEFF"+content).getBytes(StandardCharsets.UTF_16LE)));
    assertEquals(0, reg("import", file.toString()));
    var replaced= new ArrayList<Path>();
    FileAssociations.reconcile(identity+"New", s -> s.startsWith(identity), Path.of("C:\\new\\fearless.exe"), List.of(), List.of(), Path.of("C:\\new\\app.ico"), Path.of("C:\\new\\app.png"), replaced::add,
      IllegalStateException::new, m -> new IllegalStateException(m.toString()), m -> new IllegalStateException(m.toString()), IllegalStateException::new, IllegalStateException::new);
    assertEquals(List.of(), FileAssociations.identities(s -> s.startsWith(identity)));
    return replaced;
  }
  @Test void theCommandOfAnotherProgramKeepsItsSpaces(){
    assertEquals(List.of(Path.of("C:\\my apps\\fearless.exe")), replacedFrom("\"C:\\my apps\\fearless.exe\" \"%1\""));
  }
  @Test void aFamilyOpenCommandThatIsNotQuotedNamesNoCommand(){
    assertEquals(List.of(), replacedFrom("C:\\old\\fearless.exe \"%1\""));
  }
  private static int reg(String... args){
    var p= Fs.of(new ProcessBuilder(Push.of("reg", List.of(args))).redirectErrorStream(true).redirectOutput(Redirect.DISCARD)::start);
    try{ return p.waitFor(); }
    catch (InterruptedException e){ throw new AssertionError(e); }
  }
}
