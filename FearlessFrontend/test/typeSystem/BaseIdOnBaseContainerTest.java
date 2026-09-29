package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class BaseIdOnBaseContainerTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }

@Test void baseIdAsCallOnBaseContainerNamed(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[base.BaseContainer[Customer],base.BaseContainer[Person]]{ #(x)->x.as{::} }
"""));}
@Test void baseIdAsCallOnBaseContainerLambda(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[base.BaseContainer[Customer],base.BaseContainer[Person]] -> {::.as{::}} }
"""));}
@Test void baseIdAsCallOnUserAs(){fail("""
004| MyId:base.BaseId[Box[Customer],Box[Person]]{ #(x)->x.as{::} }
   |                                                    ^^^^^^^^

While inspecting the file
Type declaration "MyId" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.as[imm,Person](-.BaseId[Customer,Person]{#(_aimpl:Customer):Person->::})
""",List.of("""
Person:{}
Customer:Person{}
Box[T:*]:{ .as[T2](f: base.BaseId[T,T2]): Box[T2] -> Box[T2] }
MyId:base.BaseId[Box[Customer],Box[Person]]{ #(x)->x.as{::} }
"""));}
}
