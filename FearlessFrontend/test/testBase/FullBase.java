package testBase;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;

import message.SourceOracle;
import testUtils.FearlessTestBase;

public class FullBase extends testUtils.FearlessTestBase{
  static Path baseRoot= Path.of("C:","Users","Lardo","OneDrive","Documents","GitHub","StandardLibrary","base");
  //TODO: make a path resolver in Commons that needs an initialization set up from an ignored file
  @Test void baseFsCompiles(){ 
    SourceOracle o= FearlessTestBase.oracleFromDir(baseRoot);
    FearlessTestBase.compileAllOk(o, otherErr());
  }
}