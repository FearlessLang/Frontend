package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class BaseIdOnBaseContainerTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }

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
}
