package inferenceGrammar;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import fearlessFullGrammar.TName;
import fullWellFormedness.OtherPackages;
import fullWellFormedness.ParsePackage;
import inferenceGrammarB.Declaration;
import message.SourceOracle;
import utils.Bug;

class DbgBlock{
  static OtherPackages err(){
    return new OtherPackages(){
      public Declaration of(TName name){ throw Bug.of(); }
      public Collection<TName> dom(){ throw Bug.of(); }
    };
  }
  static OtherPackages dbg(){
    var ds= all().stream().collect(Collectors.toMap(d->d.name(),d->d));
    return new OtherPackages(){
      public Declaration of(TName name){ return ds.get(name); }
      public Collection<TName> dom(){ return ds.keySet(); }
    }; 
  }
  static String baseHead="""
    package base;
    role base000;
    """;
















































































  static String baseBody="""
Void:{}
Sealed:{}
F[R:**]: { read #: R }
F[A:**,R:**]: { read #(a: A): R }
F[A:**, B:**, R:**]: { read #(a: A, b: B): R }
F[A:**, B:**, C:**, R:**]: { read #(a: A, b: B, c: C): R }
F[A:**, B:**, C:**, D:**, R:**]: { read #(a: A, b: B, c: C, d: D): R }

MF[R:**]: { mut #: R }
MF[A:**,R:**]: { mut #(a: A): R }
MF[A:**, B:**, R:**]: { mut #(a: A, b: B): R }
MF[A:**, B:**, C:**, R:**]: { mut #(a: A, b: B, c: C): R }
MF[A:**, B:**, C:**, D:**, R:**]: { mut #(a: A, b: B, c: C, d: D): R }

ToSStr:{ read .sStr: SStr }
ToUStr:{ read .uStr: UStr }
SStr:{}
UStr:{}

SStrProcs:{
  imm .add(a:SStr,b:ToSStr): mut SStrProc -> this.add(a,b);
  }
SStrProc:{
  mut .add(a:SStr,b:ToSStr): mut SStrProc -> this.add(a,b);
  mut .build(a:SStr): SStr-> a;
  }
UStrProcs:{
  imm .add(a:UStr,b:ToUStr): mut UStrProc -> this.add(a,b);
  }
UStrProc:{
  mut .add(a:UStr,b:ToUStr): mut UStrProc -> this.add(a,b);
  mut .build(a:UStr): UStr-> a;
  }

BoolMatch[R:**]:{
  mut .true: R;
  mut .false: R;
  }
Bool: Sealed{
  .and(b: Bool): Bool;
  &&(b: mut MF[Bool]): Bool;
  &(b: Bool): Bool -> this.and(b);
  .or(b: Bool): Bool;
  |(b: Bool): Bool -> this.or(b);
  ||(b: mut MF[Bool]): Bool;
  .not: Bool;
  .if[R:**](f: mut ThenElse[R]): R;
  ?[R:**](f: mut ThenElse[R]): R -> this.if(f);
  .match[R](m: mut BoolMatch[R]): R -> this?{.then->m.true; .else->m.false};
  }
True: Bool{
  .and(b) -> b;
  &&(b) -> b#;
  .or(b) -> this;
  ||(b) -> this;
  .not -> False;
  .if(f) -> f.then;
  }
False: Bool{
  .and(b) -> this;
  &&(b) -> this;
  .or(b) -> b;
  ||(b) -> b#;
  .not -> True;
  .if(f) -> f.else;
  }
ThenElse[R:**]: { mut .then: R; mut .else: R; }

ReturnStmt[R:iso,imm,mut,read]: {mut #: R}
Condition: ReturnStmt[Bool]{}
LoopBody[R:*]: ReturnStmt[mut ControlFlow[R]]{}
Continuation[T:*,C:*,R:*]: {mut #(x: T, self: C): R}
ControlFlow: {
  .continue: mut ControlFlow[Void] -> mut ControlFlowContinue: ControlFlow[Void]{.match(m) -> m.continue};
  .break: mut ControlFlow[Void] -> mut ControlFlowBreak: ControlFlow[Void]{.match(m) -> m.break};
  .continueWith[T:*]: mut ControlFlow[T] ->  mut ControlFlowContinue[T:*]: ControlFlow[T]{.match(m) -> m.continue};
  .breakWith[T:*]: mut ControlFlow[T] -> mut ControlFlowBreak[T:*]: ControlFlow[T]{.match(m) -> m.break};
  .return[T:*](returnValue: T): mut ControlFlow[T] -> mut ControlFlowReturn[T:*]: ControlFlow[T]{
    .match(m) -> m.return(returnValue);
    mut .value: T -> returnValue;
    };
  }
ControlFlow[T:*]: {
  mut .match[R:*](m: mut ControlFlowMatch[T,R]): R -> m.continue;
  }
ControlFlowMatch[T:*,R:*]: {
  mut .continue: R;
  mut .break: R;
  mut .return(returnValue: T): R;
  }
Block: Sealed{
  #[R:*]: mut Block[R] -> {};
  #[X:**](x: X): Void -> {};
  #[X:**, R:**](_: X, res: R): R -> res;
  #[X1:**, X2:**, R:**](_: X1, _: X2, res: R): R -> res;
  #[X1:**, X2:**, X3:**, R:**](_: X1, _: X2, _: X3, res: R): R -> res;
  #[X1:**, X2:**, X3:**, X4:**, R:**](_: X1, _: X2, _: X3, _: X4, res: R): R -> res;
  }
Block[R:*]: Sealed{
  mut .done: Void -> {};
  mut .return(a: mut ReturnStmt[R]): R -> a#;
  mut .do(r: mut ReturnStmt[Void]): mut Block[R] -> this._do(r#);
    mut ._do(v: Void): mut Block[R] -> this;
  mut .let[X:*](
    x: mut ReturnStmt[X],
    cont: mut Continuation[X, mut Block[R], R]
    ): R ->
      cont#(x#, this);
  mut .openIso[X:iso,imm,mut,read](
    x: iso X,
    cont: mut Continuation[mut X, mut Block[R], R]
    ): R ->
      cont#(x, this);
  mut .if(p: mut Condition): mut BlockIf[R] -> p# ? { 'cond
    .then -> { 't
      .return(a) -> _DecidedBlock#(a#);
      .do(r) -> t._do[](r#);
        mut ._do(v: Void): mut Block[R] -> this;
      };
    .else -> { 'f
      .return(_) -> this;
      .do(_) -> this;
      };
    };
  mut .loop(body: mut LoopBody[R]): mut Block[R] -> body#.match{
    .continue -> this.loop(body);
    .break -> this;
    .return(rv) -> _DecidedBlock#rv;
    };
  }
BlockIf[R:*]:{
  mut .return(a: mut ReturnStmt[R]): mut Block[R];
  mut .do(r: mut ReturnStmt[Void]): mut Block[R];
  }
_DecidedBlock:{
  #[R:*](res: R): mut Block[R] -> { 'self
    .return(_) -> res;
    .do(_) -> self;
    .let(_, _) -> res;
    .openIso(_, _) -> res;
    .if(_) -> {
      .return(_) -> self;
      .do(_) -> self;
      };
  .loop(_) -> self;
  }
}
""";
  static List<Declaration> all(){
    var o= SourceOracle.debugBuilder()
      .put("base.fear",baseHead)
      .put("baseBody.fear","package base;\n"+baseBody)
      .build();
    return new ParsePackage()
      .of(List.of(),o.allFiles(),o,err(),0);
  }
}