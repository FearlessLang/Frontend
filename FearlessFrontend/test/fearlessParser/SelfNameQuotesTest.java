package fearlessParser;

import java.util.List;

import org.junit.jupiter.api.Test;

public class SelfNameQuotesTest extends testUtils.FearlessTestBase{
@Test void twoSelfNamesOnOneLineParse(){
  org.junit.jupiter.api.Assertions.assertEquals(1, parseFull("A:{ .a: A -> A{ 'x .a: A -> A{ 'y .a: A -> x } } }").decs().size());}
@Test void twoSelfNamesOnOneLineInTwoReceivers(){
  typeOk(List.of("B:{ .b(c: B): B -> c } A:{ .a: B -> B{ 'x .b(c: B): B -> x.b(c) }.b(B{ 'y .b(c: B): B -> y.b(c) }) }"));}
}
