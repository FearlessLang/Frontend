package fullWellFormedness;

import java.util.Map;
import java.util.List;

import fearlessFullGrammar.Declaration;
import fearlessFullGrammar.FileFull.Role;

public record Package(String name, Role role, Map<String,String> map, List<Declaration> decs, DeclaredNames names){}