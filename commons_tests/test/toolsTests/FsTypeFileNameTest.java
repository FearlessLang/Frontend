package toolsTests;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import tools.Fs;

final class FsTypeFileNameTest{
  @Test void anInnerUnderscoreCapitalisesTheNextLetter(){
    assertEquals("ExampleData", Fs.capFirst("example_data"));
    assertEquals("Mydata", Fs.capFirst("mydata"));
    assertEquals("MyData_2", Fs.capFirst("my_data_2"));
    assertEquals("A_1", Fs.capFirst("a_1"));
    assertEquals("A_", Fs.capFirst("a_"));
  }
  @Test void extraInnerUnderscoresStay(){
    assertEquals("Example_Data", Fs.capFirst("example__data"));
    assertEquals("Example__Data", Fs.capFirst("example___data"));
  }
  @Test void leadingUnderscoresStayAndTheFirstLetterIsCapitalised(){
    assertEquals("_Foo", Fs.capFirst("_foo"));
    assertEquals("__Foo", Fs.capFirst("__foo"));
    assertEquals("___A", Fs.capFirst("___a"));
    assertEquals("_FooBar", Fs.capFirst("_foo_bar"));
    assertEquals("_", Fs.capFirst("_"));
  }
  @Test void aTypeNameTurnsIntoTheFileNameCapFirstMapsBackToIt(){
    assertEquals(Optional.of("foo_bar"), Fs.fileNameOfType("FooBar"));
    assertEquals(Optional.of("_foo"), Fs.fileNameOfType("_Foo"));
    assertEquals(Optional.of("__foo_bar"), Fs.fileNameOfType("__FooBar"));
    assertEquals(Optional.of("foo_1"), Fs.fileNameOfType("Foo_1"));
    assertEquals(Optional.of("foo_b_a_r"), Fs.fileNameOfType("FooBAR"));
    assertEquals(Optional.of("example__data"), Fs.fileNameOfType("Example_Data"));
    assertEquals(Optional.of("con"), Fs.fileNameOfType("Con"));
  }
  @Test void typeNamesDifferingOnlyByCaseHaveDifferentFileNames(){
    assertEquals(Optional.of("app_log"), Fs.fileNameOfType("AppLog"));
    assertEquals(Optional.of("applog"), Fs.fileNameOfType("Applog"));
  }
  @Test void aTypeNameCapFirstNeverProducesHasNoFileName(){
    assertEquals(Optional.empty(), Fs.fileNameOfType("Foo'"));
    assertEquals(Optional.empty(), Fs.fileNameOfType("Foo_bar"));
    assertEquals(Optional.empty(), Fs.fileNameOfType("Foo$1"));
  }
  @Test void reservedDeviceNames(){
    assertEquals(true, Fs.winReserved.contains("con"));
    assertEquals(true, Fs.winReserved.contains("lpt9"));
    assertEquals(false, Fs.winReserved.contains("console"));
  }
}
