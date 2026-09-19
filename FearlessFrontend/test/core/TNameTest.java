package core;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

import utils.Pos;

class TNameTest{
  @Test void approxSpanCoversTheSimpleNameEvenWithAPackagePrefix(){
    String src= "p.Foo";
    TName n= new TName("p.Foo",0,new Pos(Pos.unknown.fileName(),1,1));
    var span= n.approxSpan().inner;
    String covered= src.substring(span.startCol()-1,span.endCol()-1);
    assertEquals("Foo",covered);
  }
}
