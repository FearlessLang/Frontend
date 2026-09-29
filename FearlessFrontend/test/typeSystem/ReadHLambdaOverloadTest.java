package typeSystem;

import java.util.List;

import org.junit.jupiter.api.Test;

public class ReadHLambdaOverloadTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }

@Test void lambdaForReadHParamDoesNotImplementDeadMutOverload(){ok(List.of("""
A:{}
Box:{ mut .get: A; read .get: A; }
Need:{ #(b: readH Box): A -> A }
User:{
  read .a: A -> A;
  read .f: A -> Need#{ .get -> this.a };
}
"""));}
@Test void lambdaForReadHReturnDoesNotImplementDeadMutOverload(){ok(List.of("""
A:{}
Box:{ mut .get: A; read .get: A; }
User:{
  read .a: A -> A;
  read .f: readH Box -> { .get -> this.a };
}
"""));}
@Test void lambdaForMutHParamImplementsBothOverloads(){ok(List.of("""
A:{}
Box:{ mut .get: A; read .get: A; }
Need:{ #(b: mutH Box): A -> A }
User:{
  read .a: A -> A;
  read .f: A -> Need#{ .get -> this.a };
}
"""));}
}