package fullWellFormedness;

import java.net.URI;
import java.util.List;

import fearlessFullGrammar.Declaration;
import message.SourceOracle;
import utils.Bug;

public class ParsePackage {
  Package of(List<URI> files, SourceOracle o){ throw Bug.of(); }
}
record Package(String name, String role, int index, List<Declaration> decs){}
